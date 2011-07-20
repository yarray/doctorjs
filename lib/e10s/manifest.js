/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an 'AS IS' basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is DoctorJS.
 *
 * The Initial Developer of the Original Code is
 * Dave Herman <dherman@mozilla.com>
 * Portions created by the Initial Developer are Copyright (C) 2010
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Dave Herman <dherman@mozilla.com>
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */

// https://developer.mozilla.org/en/chrome_registration
// http://mxr.mozilla.org/mozilla2.0/source/xpcom/components/ManifestParser.cpp


// A *path* is a string representing a filesystem path that is either absolute
// or relative to this file.

function readFile(path) {
    if (path.match(/^\//)) {
        if (typeof snarfAbs === "undefined")
            throw new ReferenceError("no snarfAbs defined");
        return snarfAbs(path);
    }
    return snarf(path);
}

// A *filename* is a string containing no directory markers ('/').

// path string -> path
function join(path, subpath) {
    return (path + "/" + subpath).replace(/\/+/, "/");
}

// path -> new Analysis
function Analysis(rootPath, warn) {
    this.rootPath = rootPath.replace(/\/+$/, "");
    this.scriptCache = { __proto__: null };
    this.manifestCache = { __proto__: null };
    // discard warnings by default
    this.warn = warn || function(){};
}

Analysis.prototype = {
    // path -> Script
    script: function(path) {
        var script = this.scriptCache[path];
        if (!script)
            script = this.scriptCache[path] = new Script(path, readFile(path));
        return script;
    },
    // path string -> Manifest
    manifest: function(dir, filename) {
        var path = join(dir, filename);
        var manifest = this.manifestCache[path];
        if (!manifest)
            manifest = this.manifestCache[path] = new Manifest(this, dir, filename, readFile(path));
        return manifest;
    },
    // -> Manifest
    chromeManifest: function() {
        return this.manifest(this.rootPath, "chrome.manifest");
    }
};

// path string -> new Script
function Script(path, src) {
    this.path = path;
    this.src = src;
    this.lines = null;
}

Script.prototype = {
    toString: function() {
        return "[Script " + this.path + "]";
    },
    toSource: function() {
        return "[Script " + this.path + "]";
    },
    countLines: function() {
        if (this.lines == null) {
            this.lines = this.src.split(/\n/).length;
        }
        return this.lines;
    }
};

// Analysis path filename string -> new Manifest
function Manifest(analysis, dir, filename, src) {
    this.analysis = analysis;
    this.dir = dir;
    this.filename = filename;
    this.src = src;

    this.parse();
    this.registerManifests();
    this.registerContent();
}

Manifest.prototype = {
    addInstr: function(key, value) {
        var a = this[key] || (this[key] = []);
        a.push(value);
    },
    parse: function() {
        var unimpl = unimplParser.bind(this);

        var instrParsers = {
            "manifest":         manifestParser.bind(this),
            "content":          contentParser.bind(this),
            "overlay":          overlayParser.bind(this),

            // probably none of these matter for the analysis
            "binary-component": unimpl,
            "interfaces":       unimpl,
            "component":        unimpl,
            "contract":         unimpl,
            "category":         unimpl,
            "locale":           unimpl,
            "skin":             unimpl,
            "style":            unimpl,
            "override":         unimpl,
            "resource":         unimpl
        };

        var lines = this.src.split(/\n/);
        for (var i = 0, n = lines.length; i < n; i++) {
            var line = lines[i].trim();
            if (line === '' || line[0] === '#')
                continue;

            var tokens = line.split(/[ \t]+/);
            var name = tokens.shift();
            var parser = instrParsers[name];

            if (!parser) {
                this.analysis.warn(this.filename + ":" + (i+1) + ": unrecognized instruction: " + name);
                continue;
            }

            var flags = popFlags(tokens, i);
            var instr = parser(name, tokens, i);
            if (instr) {
                instr.flags = flags;
                this.addInstr(name, instr);
            }
        }
    },
    registerManifests: function() {
        if (!this.manifest)
            return;
        // FIXME: read sub-manifests
    },
    registerContent: function() {
        var map = {__proto__:null};
        var content = this.content;
        for (var i = 0, n = content.length; i < n; i++) {
            var pkg = content[i]["package"];
            var uri = content[i].uri;
            if (uri.match(/^jar:/))
                uri = uri.replace(/^jar:/, "").replace(/!/g, "");
            map[pkg] = uri;
        }
        this.contentMap = map;
    },
    lookupContentURI: function(uri) {
        var match = uri.match(/^chrome:\/\/([^\/]+)\/content\/(.*)$/);
        if (!match)
            return null;
        var local = this.contentMap[match[1]];
        return local && (local + match[2]);
    },
    lookupRelativePath: function(subpath) {
        return join(this.dir, subpath);
    },
    getLocalOverlays: function() {
        var result = [];
        var overlay = this.overlay;
        for (var i = 0, n = overlay.length; i < n; i++) {
            var local = this.lookupContentURI(overlay[i].overlay);
            if (local)
                result.push(new Overlay(this, local));
        }
        return result;
    }
};

function Overlay(manifest, subpath) {
    this.manifest = manifest;
    this.subpath = subpath;
    this.allJS = null;
}

Overlay.prototype = {
    getAllJS: function() {
        if (!this.allJS) {
            var xulSrc = readFile(this.manifest.lookupRelativePath(this.subpath));
            var self = this;
            this.allJS = XUL.extractJS(xulSrc).map(function(element) {
                if (!element.uri)
                    return element;
                var local = self.manifest.lookupContentURI(element.uri);
                if (!local) {
                    return {
                        scriptType: element.scriptType,
                        uri: element.uri,
                        loaded: false
                    }
                }
                return {
                    scriptType: element.scriptType,
                    contents: self.manifest.analysis.script(self.manifest.lookupRelativePath(local)),
                    loaded: true
                };
            });
        }
        return this.allJS;
    },
    toString: function() {
        return "[Overlay " + this.subpath + "]";
    }
};

function unimplParser(name, tokens, i) {
    this.analysis.warn((i+1) + ": unhandled instruction: " + name);
    return null;
}

function manifestParser(name, tokens, i) {
    return { manifest: tokens[0] };
}

function overlayParser(name, tokens, i) {
    return { target: tokens[0], overlay: tokens[1] };
}

function contentParser(name, tokens, i) {
    return { package: tokens[0], uri: tokens[1] };
}

// Manifest.load = function(root, warn) {
//     return readLines(readFile(root + "/chrome.manifest").split(/\n/), root, warn);
// };

// array[string] -> manifest
// function readLines(lines, root, warn) {
//     // discard warnings by default
//     if (!warn)
//         warn = function(){};

//     var manifest = new Manifest(root);
//     for (var i = 0, n = lines.length; i < n; i++) {
//         var line = lines[i].trim();
//         if (line === '' || line[0] === '#')
//             continue;

//         var tokens = line.split(/[ \t]+/);
//         var name = tokens.shift();
//         var parser = instrParsers[name];

//         if (!parser) {
//             warn("chrome.manifest:" + (i+1) + ": unrecognized instruction: " + name);
//             continue;
//         }

//         var flags = popFlags(tokens, i, warn);
//         var instr = parser(name, tokens, i, warn);
//         if (instr) {
//             instr.flags = flags;
//             manifest.addInstr(name, instr);
//         }
//     }
//     manifest.registerContent();
//     return manifest;
// }

var flagParsers = {
    "application":       equalityParser,
    "appversion":        inequalityParser,
    "contentaccessible": equalityParser,
    "os":                equalityParser,
    "osversion":         inequalityParser,
    "abi":               equalityParser
};

function equalityParser(token) {
    var i = token.indexOf("=");
    return {
        flag: token.substring(0, i).trim(),
        value: token.substring(i + 1).trim()
    };
}



function inequalityParser(token) {
    var keys = ["<=", ">=", "<", ">", "="];
    for (var i = 0, n = keys.length; i < n; i++) {
        var relation = keys[i];
        var idx = token.indexOf(relation);
        if (idx >= 0) {
            return {
                flag: token.substring(0, idx).trim(),
                relation: relation,
                value: token.substring(idx + relation.length).trim()
            };
        }
    }
}

// array[string] nat -> array[object]
function popFlags(tokens, i) {
    var flags = [];

    // keep popping until a token doesn't parse as a flag
  parseNext:
    for (var j = tokens.length - 1; j >= 0; j--) {
        var token = tokens[j];

        // find a parser for this flag
        for (var flag in flagParsers) {
            if (token.substring(0, flag.length) === flag) {
                var parsed = flagParsers[flag](token);
                if (parsed) {
                    flags.unshift(parsed);
                    continue parseNext;
                }
            }
        }

        // we couldn't find a parser, so bail
        break;
    }

    return flags.length > 0 ? flags : null;
}
