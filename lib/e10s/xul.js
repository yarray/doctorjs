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

var XUL = (function() {

function reader(inits) {
    var r = XMLReaderFactory.createXMLReader();
    var h = new DefaultHandler2();
    for (var key in inits) {
        if (inits.hasOwnProperty(key)) {
            h[key] = inits[key];
        }
    }
    r.setHandler(h);
    return r;
}

// https://developer.mozilla.org/en/XUL/Events
var nonAttributeEvents = [
    // Window activation events
    "activate", "deactivate",

    // Inherited DOM events
    "DOMMouseScroll",

    // Mutation DOM events
    "DOMAttrModified", "DOMAttrInserted", "DOMNodeRemoved",

    // Common XUL events
    "DOMMenuItemActive", "DOMMenuItemInactive",

    // Accessibility events
    "CheckboxStateChange", "RadioStateChange"
];

var attributeEvents = [
    // Inherited DOM events
    "blur", "change", "click", "dblclick", "focus",
    "keydown", "keypress", "keyup", "load", "mousedown", "mousemove", "mouseout",
    "mouseover", "mouseup", "select", "unload",

    // Common XUL Events
    "broadcast", "close", "command", "commandupdate", "contextmenu",
    "drag", "dragdrop", "dragend", "dragenter", "dragexit",
    "draggesture", "dragover", "input", "overflow", "popuphidden",
    "popuphiding", "popupshowing", "popupshown", "syncfrompreference",
    "synctopreference", "underflow"
];

var attributeEventMap = (function() {
    var result = {};
    for (var i = 0, n = attributeEvents.length; i < n; i++) {
        result["on" + attributeEvents[i]] = true;
    }
    return result;
})();

// FIXME: need more
var xulElementTags = [
    "button", "command", "commandset", "notificationbox",
    "menu", "menupopup", "menuitem", "menuseparator", "menulist",
    "keyset", "key", "tooltip", "hbox", "grid", "splitmenu",
    "toolbarbutton", "toolbarspacer", "treecols", "treecol", "splitter", "treechildren",
    "vbox", "statusbar", "statusbarpanel", "label", "window",
    "preferences", "prefpane", "scale", "tree", "textbox", "checkbox", "saveddropdown",
    "description", "script"
];

var xulElementTagMap = (function() {
    var result = {};
    for (var i = 0, n = xulElementTags.length; i < n; i++) {
        result[xulElementTags[i]] = true;
    }
    return result;
})();

function isXULElement(tag) {
    return xulElementTagMap.hasOwnProperty(tag);
}

var inlineEventHandlers = {
    "command":       ["oncommand"],
    "toolbarbutton": ["oncommand"],
    "key":           ["oncommand"],
    "menuitem":      ["oncommand"],
    "description":   ["onclick"],
    "button":        ["oncommand"],
    "menupopup":     ["onpopupshowing"],
    "saveddropdown": ["onchange"],
    "checkbox":      ["oncommand", "onsynctopreference", "onsyncfrompreference"],
    "prefpane":      ["onpaneload"],
    "scale":         ["onchange"],
    "tree":          ["onselect"],
    "textbox":       ["oninput", "onblur"],
    "label":         ["onclick"]
};

function Context() {
    this.frames = [];
}

Context.prototype = {
    push: function(frame) {
        this.frames.push(frame);
    },
    top: function() {
        if (this.isEmpty())
            throw new Error("empty context");
        return this.frames[this.frames.length - 1];
    },
    pop: function() {
        return this.frames.pop();
    },
    isEmpty: function() {
        return this.frames.length < 1;
    },
    currentTag: function() {
        if (this.isEmpty())
            return null;
        return this.top().tag;
    }
};

function extractJS(src) {
    var js = [];
    var cx = new Context();
    var xul = reader({
        startElement: function(uri, localName, qName, attrs) {
            if (qName === "script") {
                var attr = attrs.getValue("src");
                if (attr)
                    js.push({ scriptType: attrs.getValue("type"), uri: attr });
                else
                    cx.push({ tag: "script", type: attrs.getValue("type") });
            } else if (inlineEventHandlers.hasOwnProperty(qName)) {
                var eventTypes = inlineEventHandlers[qName];
                for (var i = 0, n = eventTypes.length; i < n; i++) {
                    var eventType = eventTypes[i];
                    var attr = attrs.getValue(eventType);
                    if (attr)
                        js.push({ tag: qName, eventType: eventType.replace(/^on/, ""), handler: attr });
                }
            }
        },
        endElement: function(uri, localName, qName) {
            if (qName === "script" && !cx.isEmpty())
                cx.pop();
        },
        characters: function(cs) {
            if (cx.currentTag() === "script") {
                var top = cx.top();
                js.push({ scriptType: top.type, src: cs });
            }
        }
    });
    xul.parseString(src);
    return js;
}

return {
    extractJS: extractJS
};

})();

// var elements = {
//     overlay: function(elt) { },
//     window: function(elt) { },
//     notificationbox: function(elt) { },
//     menubar: function(elt) { },
//     menu: function(elt) { },
//     menupopup: function(elt) { },
//     menuitem: function(elt) { },
//     menuseparator: function(elt) { },
// };

// function extractOverlays(src) {
//     var cx = { parent: null, element: null };
//     var xul = reader({
//         startElement: function(uri, localName, qName, attrs) {
//             var parent = cx;
//             if (qName in elements) {
//             var element;
//             switch (qName) {
//               case "overlay":
//                 element = {
//                     type: "overlay",
//                     windows: [],
//                     notificationBoxes: []
//                 };
//                 cx = { parent: parent, element: element };
//                 break;

//               case "window":
//                 element = {
//                     type: 
//                 };

//               case "notificationbox":
//               case "menubar":
//               case "menu":
//               case "menupopup":
//               case "menuitem":
//               case "menuseparator":
//               default:
//             }
//         }
//     });
// }
