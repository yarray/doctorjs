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

var Smoosh = (function() {

function coords(path, jses, jsms, xuls) {
}

// function coords(path) {
//     var currentLine = 0;

//     print("[");

//     (new Analysis(path)).chromeManifest().getLocalOverlays().forEach(function(overlay) {
//         overlay.getAllJS().forEach(function(script, i) {
//             if (!script.loaded)
//                 return;
//             print((i > 0 ? ", " : "") + '{ "line" : ' + currentLine + ', "path" : ' + uneval(script.contents.path) + " }");
//             currentLine += script.contents.countLines();
//         });
//     });

//     print("]");
// }

function smoosh(path, jses, jsms, xuls) {
    var currentLine = 0;

    function spew(file) {
        var src = snarfAbs(path + "/" + file);
        currentLine += src.split(/\n/).length;
        print(src);
    }

    jses.forEach(spew);
    jsms.forEach(spew);

    xuls.forEach(function(file) {
        
    });
    // FIXME: xuls
}

// function smoosh(path) {
//     var currentLine = 0;

//     var analysis = new Analysis(path);
//     var manifest = analysis.chromeManifest();
//     var overlays = manifest.getLocalOverlays();
//     overlays.forEach(function(overlay) {
//         var allJS = overlay.getAllJS();
//         allJS.forEach(function(script) {
//             if (!script.loaded)
//                 return;
//             currentLine += script.contents.countLines();
//             print(script.contents.src);
//         });
//     });
// }

return {
    smoosh: smoosh,
    coords: coords
};

})();
