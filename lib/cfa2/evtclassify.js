#!/usr/bin/env node
;

var path = require('path');
var fs = require("fs");
var print = console.log,
    readFileSync = require('fs').readFileSync,
    spawn = require('child_process').spawn,
    parse = require('../../narcissus/lib/parser').parse,
    desugar = require('../../narcissus/lib/desugaring').desugar,
    classify_events = require('./jscfa').classify_events;

function printf(fd,s) { fs.writeSync(fd, s, null, 'utf8'); }

var addon = process.argv[2];
var resultsDir = process.argv[3] || ".";

try {
  var ast = desugar(parse(readFileSync(addon), addon, 1));
  var lines = ast.tokenizer.source.split("\n");
  var evts = classify_events(ast);
  var fd = fs.openSync(path.join(resultsDir, "evts"), "w", 0777);

  printf(fd,
         normStr("*Source code*", 80) + normStr("*Event name*", 20) +
         normStr("*Attached on*", 14) + normStr("*Came from*", 12) +
         "*Status*\n\n");

  var safe = 0;
  for (var e in evts) {
    var ans = evts[e], r;
    if (r = ans.result) {
      if (r[3] === "safe") ++safe;
      printf(fd,
             normStr(lines[ans.lineno - 1].replace(/^\s+/,""), 75) + "     " + 
             normStr(r[0].slice(0, -1), 20) + normStr(r[1], 14) + 
             normStr(r[2], 12) + r[3] + "\n");
    }
  }
  printf(fd, "\n");
  printf(fd, "Total: " + evts.analyzed + ",   Safe: " + safe + "\n");
  fs.closeSync(fd);
  printResult("done");
} catch (e) {
  printResult("failed", e && e.stack);
  process.exit(1);
}

function printResult(result, extras) {
  try {
    var fd = fs.openSync(path.join(resultsDir, "result"), "w", 0777);
    printf(fd, result + "\n");
    if (extras)
        printf(fd, extras);
    fs.closeSync(fd);
  } catch (e) { }
}

function normStr(s, l) {
  var diff = l - s.length;

  if (diff > 0)
    for (var i = 0; i < diff; i++) s += " ";
  else
    s = s.slice(0, s.length + diff);
  return s;
}
