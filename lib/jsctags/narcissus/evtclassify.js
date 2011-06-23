#!/usr/bin/env node
;

var print = console.log,
readFileSync = require('fs').readFileSync,
spawn = require('child_process').spawn,
parse = require('./jsparse').parse,
classify_events = require('./jscfa').classify_events;

var addon = process.argv[2];
var ast = parse(readFileSync(addon), addon, 1);
var lines = ast.tokenizer.source.split("\n");
var evts = classify_events(ast);
var fs = require("fs"), fd = fs.openSync("evts", "w", mode=0777);

function printf(s) { fs.writeSync(fd, s, null, encoding='utf8'); }

printf(normStr("*Source code*", 80) + normStr("*Event name*", 20) +
       normStr("*Attached on*", 14) + normStr("*Came from*", 12) +
       "*Status*\n\n");

var safe = 0;
for (var e in evts) {
  var ans = evts[e], r;
  if (r = ans.result) {
    if (r[3] === "safe") ++safe;
    printf(normStr(lines[ans.lineno - 1], 75) + "     " + 
           normStr(r[0].slice(0, -1), 20) + normStr(r[1], 14) + 
           normStr(r[2], 12) + r[3] + "\n");
  }
}
printf("\n");
printf("Total: " + evts.analyzed + ",   Safe: " + safe + "\n");
fs.closeSync(fd);

function normStr(s, l) {
  var diff = l - s.length;

  if (diff > 0)
    for (var i = 0; i < diff; i++) s += " ";
  else
    s = s.slice(0, s.length + diff);
  return s;
}
