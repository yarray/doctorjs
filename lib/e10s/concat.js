#!/usr/bin/env node

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

var path = require("path");
var fs = require("fs");
var async = require("async");

var xul = require("./xul");

function concat(root, jses, jsms, xuls, pureJSOut, wrappedJSOut, coordsOut) {
    var currentLine = 1;
    var coords = {};

    var pureJSStream = fs.createWriteStream(pureJSOut, { encoding: 'utf8' });
    var wrappedJSStream = fs.createWriteStream(wrappedJSOut, { encoding: 'utf8' });

    function countLines(str) {
        var matches = str.match(/\n/g);
        if (matches)
            currentLine += matches.length;
    }

    function puts(str, cb, wrappedStr) {
        var toDrain = [];
        if (!pureJSStream.write(str))
            toDrain.push(pureJSStream);
        if (!wrappedJSStream.write(wrappedStr || str))
            toDrain.push(wrappedJSStream);

        if (toDrain.length === 0) {
            process.nextTick(cb);
        } else {
            async.forEachSeries(toDrain, function(stream, cb) {
                stream.once("drain", cb);
            }, cb);
        }
    }

    function cat(file, cb) {
        if (wrappedJSStream.write("(function(){"))
            process.nextTick(catBody);
        else
            wrappedJSStream.once("drain", catBody);

        function catBody() {
            coords[file] = currentLine;
            var stream = fs.createReadStream(path.join(root, file));
            stream.setEncoding("utf8");
            stream.on("data", countLines);
            stream.pipe(pureJSStream, { end: false });
            stream.pipe(wrappedJSStream, { end: false });
            stream.on("end", function(err) {
                if (err) {
                    cb(err);
                    return;
                }
                currentLine++;
                puts("\n", cb, "\n})();\n");
            });
        }
    }

    function wrapHandler(filename, lineno, contents) {
        // munge the handler name
        var munged = filename.replace(/[.\/]/g, "_").replace(/[^a-z0-9_$]*/g, "");
        var handler = "$handler_" + munged + "_" + lineno;

        // protect against a line comment on the last line
        var endLineComment = /\/\/([^\n]*)$/;
        var match = contents.match(endLineComment, "/*$1*/");
        if (match) {
            var comment = match[1];
            comment = comment.replace(/\*\//g, "__");
            contents = contents.replace(endLineComment, "/*" + comment + "*/");
        }

        return "function " + handler + "(event) { " + contents + "}";
    }

    function print(file) {
        return function printScript(script, cb) {
            if (script.contents) {
                var contents = script.eventType
                             ? wrapHandler(file, script.line, script.contents)
                             : script.contents;
                contents = contents + "\n";
                if (!coords[file])
                    coords[file] = {};
                coords[file][script.line] = currentLine;
                countLines(contents);
                puts(contents, cb);
            } else {
                process.nextTick(cb);
            }
        };
    }

    function extract(file, cb) {
        xul.extractScripts(path.join(root, file), function(err, scripts) {
            if (!err)
                async.forEachSeries(scripts, print(file), cb);
            else
                process.nextTick(function() { cb(err) });
        });
    }

    async.series([
        function(next) { async.forEachSeries(jses, cat, next) },
        function(next) { async.forEachSeries(jsms, cat, next) },
        function(next) { async.forEachSeries(xuls, extract, next) },
        function(next) {
            pureJSStream.end();
            wrappedJSStream.end();
            var coordsStream = fs.createWriteStream(coordsOut, { encoding: 'utf8' });
            coordsStream.write(JSON.stringify(coords));
            coordsStream.end();
        }
    ]);
}

function main(args) {
    var root = args[0];
    var jses = JSON.parse(args[1]);
    var jsms = JSON.parse(args[2]);
    var xuls = JSON.parse(args[3]);
    var pureJS = args[4];
    var wrappedJS = args[5];
    var coords = args[6];
    concat(root, jses, jsms, xuls, pureJS, wrappedJS, coords);
}

main(process.argv.slice(2));
