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
 * The Original Code is Bespin.
 *
 * The Initial Developer of the Original Code is
 * Dimitris Vardoulakis <dimvar@gmail.com>
 * Portions created by the Initial Developer are Copyright (C) 2010
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Dimitris Vardoulakis <dimvar@gmail.com>
 *   Patrick Walton <pcwalton@mozilla.com>
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

/*
 * Narcissus - JS implemented in JS.
 *
 * Control-flow analysis to infer types. The output is in ctags format.
 */


/* (Possible) TODOs:
 * - now all objs are in heap. If it's too imprecise, treat them as heap vars.
 *   Create on stack & heap, and if heap changes when u need the obj then join.
 * - representation of Aobj: in the common case, an abstract obj has one proto 
 *   and one constructor. Specialize for this case.
 */

/*
 * Semantics of: function foo (args) body:
 * It's not the same as: var foo = function foo (args) body
 * If it appears in a script then it's hoisted at the top, so it's in funDecls
 * If it appears in a block then it's visible after it's appearance, in the
 * whole rest of the script!!
 * {foo(); {function foo() {print("foo");}}; foo();}
 * The 1st call to foo throws, but if you remove it the 2nd call succeeds.
 */

/* (POSSIBLY) UNSOUND ASSUMPTIONS:
 * - Won't iterate loops to fixpt.
 * - Return undefined not tracked, eg (if sth return 12;) always returns number.
 * - If the prototype property of a function object foo is accessed in a weird
 *   way, eg foo["proto" + "type"] the analysis won't figure it out.
 * - when popping from an array, I do nothing. This is hard to make sound.
 */

////////////////////////////////////////////////////////////////////////////////
/////////////////////////////   UTILITIES  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

if (!Array.prototype.forEach) 
  Array.prototype.forEach = function(fun) {
    for (var i = 0, len = this.length; i < len; i++) 
      /* if (i in this) */ fun(this[i], i, this);
  };

// search for an elm in the array that satisfies pred
Array.prototype.member = function(pred) {
  for (var i = 0, len = this.length; i < len; i++)
    /* if (i in this) */ if (pred(this[i])) return this[i];
  return false;
};

// starting at index, remove all elms that satisfy the pred in linear time.
Array.prototype.rmElmAfterIndex = function(pred, index) {
  if (index >= this.length) return;
  for (var i = index, j = index, len = this.length; i < len; i++)
    if (!pred(this[i])) this[j++] = this[i];
  this.length = j;
};

// remove all duplicates from array (keep first occurence of each elm)
// pred determines the equality of elms
Array.prototype.rmDups = function(pred) {
  var i = 0, self = this;
  while (i < (this.length - 1)) {
    this.rmElmAfterIndex(function(elm) { return pred(elm, self[i]); }, i+1);
    i++;
  }
};

// compare two arrays for structural equality
function arrayeq(eq, a1, a2) {
  var len = a1.length, i;
  if (len !== a2.length) return false;
  for (i=0; i<len; i++) if (!eq(a1[i], a2[i])) return false;
  return true;
}

function buildArray(size, elm) {
  var a = new Array(size);
  for (var i=0; i<size; i++) a[i] = elm;
  return a;
}

function buildString(size, elm) {
  return buildArray(size, elm).join("");
}

// merge two sorted arrays of numbers into a sorted new array, remove dups!
function arraymerge(a1, a2) {
  var i=0, j=0, len1 = a1.length, len2 = a2.length, a = new Array();
  while (true) {
    if (i === len1) {
      for (; j < len2; j++) a.push(a2[j]);
      return a;
    }
    if (j === len2) {
      for (; i<len1; i++) a.push(a1[i]);
      return a;
    }
    var diff = a1[i] - a2[j];
    if (diff < 0)
      a.push(a1[i++]);
    else if (diff > 0)
      a.push(a2[j++]);
    else
      i++;
  }
}

const UNHANDLED_CONSTRUCT = 0;
const CFA_ERROR = 1;
// number, string -> Error
// returns an Error w/ a "code" property, so that DrJS can classify errors
function errorWithCode(code, msg) {
  var e = new Error(msg);
  e.code = code;
  return e;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////    PREPARE AST FOR FLOW ANALYSIS    ///////////////////////
////////////////////////////////////////////////////////////////////////////////

var m_jsdefs = require('./jsdefs');
var jsparse = require('./jsparse');
var Node = jsparse.Node;
const DECLARED_FORM = jsparse.DECLARED_FORM;

eval(m_jsdefs.defineTokenConstants());

var print = console.log;

// count is used to generate a unique ID for each node in the AST.
var count;

// Instead of a flat long case dispatch, arities create a tree-like dispatch.
// Nodes are grouped in arities by how we recur down their structure.
var opArity = [];

const NULLARY = 0, UNARY = 1, BINARY = 2, TERNARY = 3, MULTI = 4,
MULTI_OI = 5, MULTI_CALL = 6, FUN = 7, NULLARY_OR_UNARY = 8;

opArity[NULL] = opArity[THIS] = opArity[TRUE] = opArity[FALSE] = NULLARY;
opArity[IDENTIFIER] = opArity[NUMBER] = opArity[STRING] = NULLARY;
opArity[REGEXP] = NULLARY;

opArity[DELETE] = opArity[VOID] = opArity[TYPEOF] = opArity[NOT] = UNARY;
opArity[BITWISE_NOT] = opArity[UNARY_PLUS] = opArity[UNARY_MINUS] = UNARY;
opArity[NEW] = opArity[GROUP] = opArity[INCREMENT] = opArity[DECREMENT] = UNARY;

opArity[BITWISE_OR] = opArity[BITWISE_XOR] = opArity[BITWISE_AND] = BINARY;
opArity[EQ] = opArity[NE] = opArity[STRICT_EQ] = opArity[STRICT_NE] = BINARY;
opArity[LT] = opArity[LE] = opArity[GE] = opArity[GT] = BINARY;
opArity[INSTANCEOF] = opArity[LSH] = opArity[RSH] = opArity[URSH] = BINARY;
opArity[PLUS] = opArity[MINUS] = opArity[MUL] = opArity[DIV] = BINARY;
opArity[MOD] = opArity[DOT] = opArity[AND] = opArity[OR] = BINARY; 
opArity[ASSIGN] = opArity[INDEX] = opArity[IN] = opArity[DOT] = BINARY;

opArity[HOOK] = TERNARY;
opArity[COMMA] = opArity[ARRAY_INIT] = MULTI;
opArity[OBJECT_INIT] = MULTI_OI;
opArity[CALL] = opArity[NEW_WITH_ARGS] = MULTI_CALL;
opArity[FUNCTION] = FUN;
opArity[YIELD] = NULLARY_OR_UNARY;

// el hacko grande: need new expression token but don't know the token id`s 
// (eval`d from jsdefs). No conflict w/ IF b/c it only appears as a stm.
const DOT_PROTO = IF;
opArity[DOT_PROTO] = UNARY;
const ARGUMENTS = FOR;
opArity[ARGUMENTS] = UNARY;
const PLUS_ASSIGN = WHILE;
opArity[PLUS_ASSIGN] = BINARY;

// expr node -> stm node
function semiNode(n) {
  var sn = new Node(n.tokenizer, SEMICOLON);
  sn.expression = n;
  return sn;
}

// tokenizer, string -> identifier node
function idNode(t, name) {
  var n = new Node(t, IDENTIFIER);
  n.name = n.value = name;
  return n;
}

// node, optional string -> node
// Does some cleanup on the input expression node in-place.
// funName is used to name some anonymous funs using heuristics from the context
function fixExp(n, funName) {
  var nt = n.type;

  function fixe(n, i, parent) { parent[i] = fixExp(n); }

  switch (opArity[nt]) {
  case BINARY:
    if (nt === INDEX) {
      n.forEach(fixe);
      if (n[1].type === NUMBER) {
        n[1].type = STRING;
        n[1].value += "-";
      }
      return n;
    }
    else if (nt === DOT) {
      // DOT_PROTO has no new semantic meaning, it's an optimization so that we
      // dont check at every property access if the property name is "prototype"
      if (n[1].value === "prototype") n.type = DOT_PROTO;
      n[1].value += "-";
    }
    else if (nt === ASSIGN && n[0].assignOp === PLUS)
      n.type = PLUS_ASSIGN;
    else if (nt === ASSIGN && !n[0].assignOp) {
      var n0 = n[0];
      n[0] = fixExp(n0);
      if (n0.type === IDENTIFIER)
        funName = n0.name;
      else if (n0.type === DOT)
        funName = n0[1].name.substring(0, n0[1].name.length - 1);
      n[1] = fixExp(n[1], funName);
      return n;
    }
    //fall thru
  case TERNARY: case MULTI:
    n.forEach(fixe);
    return n;

  case MULTI_CALL:
    n[0] = fixExp(n[0]);
    n[1].forEach(fixe);
    return n;

  case NULLARY:
    if (nt === IDENTIFIER) n.name = n.value;
    else if (nt === STRING) n.value += "-";
    return n;

  case UNARY:
    if (nt === GROUP) return fixExp(n[0]);
    if (nt === UNARY_MINUS && n[0].type === NUMBER) {
      n.type = NUMBER;
      n.value = -n[0].value;
      n.splice(0, 1);
      return n;
    }
    if (nt === NEW) { // unify NEW and NEW_WITH_ARGS
      n.type = NEW_WITH_ARGS;
      n[1] = [];
    }
    n[0] = fixExp(n[0]);
    return n;

  case FUN:
    fixFun(n, funName);
    return n;

  case MULTI_OI:
    n.forEach(function(prop) {
      if (prop.type === GETTER || prop.type === SETTER) {
        fixFun(prop, prop.name);
        return;
      }

      var pname = prop[0].value;
      prop[0] = idNode(prop[0].tokenizer, pname + "-");
      prop[1] = fixExp(prop[1], pname);
    });
    return n;

  case NULLARY_OR_UNARY:    // yield
    if (n.value != null) fixExp(n.value);
    return n;
  }
}

// node, optional string -> void
function fixFun(n, funName) {
  var t = n.tokenizer;
  // replace name w/ a property fname which is an IDENTIFIER node.
  n.fname = idNode(t, n.name || funName);
  delete n.name;
  // turn the formals to nodes, I'll want to attach stuff to them later.
  n.params.forEach(function(p, i, ps) { ps[i] = idNode(t, p); });
  // don't tag builtin funs, they never have RETURN when used as constructors.
  n.hasReturn = fixStm(n.body);
}

// node -> boolean
// returns true iff n contains RETURN directly (not RETURNs of inner functions).
function fixStm(n) {
  var i, j, n2, n3, ans1, ans2;
  
  // VAR or CONST node -> comma node
  // Convert to assignments, with readOnly field for constants.
  // The returned node may contain 0 subexpressions.
  function initsToAssigns(n) {
    var n2, vdecl, a, initv, i, len;
    
    n2 = new Node(n.tokenizer, COMMA);
    for (i=0, len=n.length; i < len; i++) {
      vdecl = n[i];
      initv = vdecl.initializer;
      if (initv) {
        initv = fixExp(initv, vdecl.name);
        a = new Node(vdecl.tokenizer, ASSIGN);
        a.push(idNode(vdecl.tokenizer, vdecl.name));
        a.push(initv);
        a.readOnly = vdecl.readOnly;
        n2.push(a);
      }
    }
    return n2;
  }

  switch (n.type) {
  case SCRIPT:
  case BLOCK:
    var n2t, ans1 = false;
    i=0;
    while (i < n.length) {
      n2 = n[i];
      switch (n2.type) {
      case VAR:
      case CONST:
      case LET_DEF:
        n3 = initsToAssigns(n2);
        if (n3.length > 0) {
          var semin = semiNode(n3);
          n.splice(i++, 1, semin);
        }
        else n.splice(i, 1);
        break;

      case SWITCH:
        if (n2.cases.length === 0) {// switch w/out branches becomes semi node
          n2.discriminant = fixExp(n2.discriminant);
          n[i] = semiNode(n2.discriminant);
        }
        else
          ans1 = fixStm(n2) || ans1;
        i++;
        break;

      case BREAK:
      case CONTINUE: //rm break & continue nodes
        n.splice(i, 1);
        break;

      case FUNCTION: //rm functions from Script bodies, they're in funDecls
        fixFun(n2);
        if (n2.functionForm === DECLARED_FORM)
          n.splice(i, 1);
        else
          ++i;
        break;

      case LABEL: //replace LABEL nodes by their statement (forget labels)
        n[i] = n2.statement;
        break;
        
      case SEMICOLON: // remove empty SEMICOLON nodes
        if (n2.expression == null) {
          n.splice(i, 1);
          break;
        } // o/w fall thru to fix the node
        
      default:
        ans1 = fixStm(n2) || ans1;
        i++;
        break;
      }
    }
    return ans1;

  case BREAK: case CONTINUE:
    n.type = BLOCK;
    return false;

  case SEMICOLON:
    if (!n.expression)
      n.type = BLOCK;
    else
      n.expression = fixExp(n.expression); //n.expression can't be null
    return false;

  case IF:
    n.condition = fixExp(n.condition);
    ans1 = fixStm(n.thenPart);
    return (n.elsePart && fixStm(n.elsePart)) || ans1;

  case SWITCH:
    n.discriminant = fixExp(n.discriminant);
    ans1 = false;
    n.cases.forEach( function(branch) {
      branch.caseLabel && (branch.caseLabel = fixExp(branch.caseLabel));
      ans2 = fixStm(branch.statements);
      ans1 = ans1 || ans2;
    });
    return ans1;

  case FOR:
    n2 = n.setup;
    if (n2) {
      if (n2.type === VAR || n2.type === CONST)
        n.setup = initsToAssigns(n2);
      else
        n.setup = fixExp(n2);
    }
    n.condition && (n.condition = fixExp(n.condition));
    n.update && (n.update = fixExp(n.update));
    return fixStm(n.body);

  case FOR_IN:
    n.iterator = fixExp(n.iterator);
    n.object = fixExp(n.object);
    return fixStm(n.body);
    
  case WHILE:
  case DO:
    n.condition = fixExp(n.condition);
    return fixStm(n.body);

  case TRY: // turn the varName of each catch-clause to a node called exvar
    ans1 = fixStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) {
      clause.exvar = idNode(clause.tokenizer, clause.varName);
      clause.guard && (clause.guard = fixExp(clause.guard));
      ans2 = fixStm(clause.block);
      ans1 = ans1 || ans2;
    });
    return (n.finallyBlock && fixStm(n.finallyBlock)) || ans1;

  case THROW: 
    n.exception = fixExp(n.exception);
    return false;

  case RETURN:
    if (n.value === "return")
      n.value = idNode(n.tokenizer, "undefined");
    else
      n.value = fixExp(n.value);
    return true;
     
  case VAR: case CONST: // very rare to not appear in a block or script.
    n2 = initsToAssigns(n);
    n.type = SEMICOLON;
    n.expression = n2;
    n.length = 0;
    return false;
   
  case WITH:
    throw errorWithCode(UNHANDLED_CONSTRUCT, "fixStm: WITH not implemented");

  default:
    throw errorWithCode(UNHANDLED_CONSTRUCT,
                        "fixStm: " + n.type + ", line " + n.lineno);
  }
}

// Invariants of the AST after fixStm:
// - no GROUP nodes
// - no NEW nodes, they became NEW_WITH_ARGS
// - the formals of functions are nodes, not strings
// - functions have a property fname which is an IDENTIFIER node, name deleted
// - no VAR and CONST nodes, they've become semicolon comma nodes.
// - no BREAK and CONTINUE nodes.
//   Unfortunately, this isn't independent of exceptions.
//   If a finally-block breaks or continues, the exception isn't propagated.
//   I will falsely propagate it (still sound, just more approximate).
// - no LABEL nodes
// - function nodes only in blocks, not in scripts
// - no empty SEMICOLON nodes
// - no switches w/out branches
// - each catch clause has a property exvar which is an IDENTIFIER node
// - all returns have .value (the ones that didn't, got an undefined)
// - the lhs of a property initializer of an OBJECT_INIT is always an identifier
// - the property names in DOT and OBJECT_INIT end with a dash.
// - there is no DOT whose 2nd arg is "prototype", they've become NODE_PROTOs.
// - value of a NUMBER can be negative (UNARY_MINUS of constant became NUMBER).
// - the operator += has its own non-terminal, PLUS_ASSIGN.
// - each function node has a property hasReturn to show if it uses RETURN.
// - there is no INDEX whose 2nd arg has type NUMBER, they've become STRINGs.

// node -> undefined
// adds an "addr" property to nodes which is a number unique for each node.
function labelExp(n) {
  switch (opArity[n.type]) {
  case MULTI:
    if (n.type === ARRAY_INIT) n.addr = ++count;
    //fall thru
  case UNARY: case BINARY: case TERNARY:
    n.forEach(labelExp);
    return;

  case MULTI_CALL:
    if (n.type === NEW_WITH_ARGS) n.addr = ++count;
    labelExp(n[0]);
    n[1].forEach(labelExp);
    return;

  case NULLARY:
    if (n.type === REGEXP) n.addr = ++count;
    return;

  case FUN:
    labelFun(n);
    return;

  case MULTI_OI:
    n.addr = ++count;
    n.forEach(function(prop) {
      if (prop.type === GETTER || prop.type === SETTER) {
        labelFun(prop);
        return;
      }

      labelExp(prop[0]); labelExp(prop[1]);
    });
    return;
  }
}

function labelFun(n) {
  n.addr = ++count;
  n.defaultProtoAddr = ++count;
  n.fname.addr = ++count;
  n.params.forEach( function(p) { p.addr = ++count; });
  labelStm(n.body);
}

// node -> node
// adds an "addr" property to nodes, which is a number unique for each node.
function labelStm(n) {
  switch (n.type) {
  case SCRIPT:
    n.varDecls.forEach(function(vd) {vd.addr = ++count;});
    n.funDecls.forEach(labelFun);
    // fall thru to fix the script body
  case BLOCK:
    n.forEach(labelStm);
    break;

  case FUNCTION:
    labelFun(n);
    break;

  case SEMICOLON:
    labelExp(n.expression); 
    break;

  case IF:
    labelExp(n.condition);
    labelStm(n.thenPart);
    n.elsePart && labelStm(n.elsePart);
    break;
        
  case SWITCH:
    labelExp(n.discriminant);
    n.cases.forEach(function(branch) {
      branch.caseLabel && labelExp(branch.caseLabel);
      labelStm(branch.statements);
    });
    break;

  case FOR: 
    n.setup && labelExp(n.setup);
    n.condition && labelExp(n.condition);
    n.update && labelExp(n.update);
    labelStm(n.body);
    break;

  case FOR_IN:
    labelExp(n.iterator);
    labelExp(n.object);
    labelStm(n.body);
    break;

  case WHILE: case DO:
    labelExp(n.condition);
    labelStm(n.body);
    break;

  case TRY:
    labelStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) {
      labelExp(clause.exvar);
      clause.guard && labelExp(clause.guard);
      labelStm(clause.block);
    });
    n.finallyBlock && labelStm(n.finallyBlock);
    break;

  case THROW: 
    labelExp(n.exception);
    break;

  case RETURN:
    labelExp(n.value);
    break;

  default:
    throw errorWithCode(UNHANDLED_CONSTRUCT, "labelStm: unknown case");
  }
  return n;
}


// FIXME: if speed of frame lookups becomes an issue, revisit tagVarRefs and
// turn frame lookups to array accesses instead of property accesses.

const STACK = 0, HEAP = 1;

// jump table for tagging variable references
var tagVarRefsExp = [];

(function() {
  // node, array of id nodes, array of id nodes -> undefined
  // classify variable references as either stack or heap variables.

  function _binary(n, innerscope, otherscopes) {
    if (n.type === DOT) {// don't classify property names
      var n0 = n[0];
      if (commonJSmode && n0.type === IDENTIFIER && n0.name === "exports")
        tagVarRefsExp[opArity[n0.type]](n0, innerscope, otherscopes, n[1]);
      else 
        tagVarRefsExp[opArity[n0.type]](n0, innerscope, otherscopes);
      return;
    }
    else if (n.type === INDEX) {
      var n0 = n[0], shadowed = false;
      // use new non-terminal only  if "arguments" refers to the arguments array
      if (n0.type === IDENTIFIER && n0.name === "arguments") {
        for (var i = innerscope.length - 1; i >= 0; i--) 
          if (innerscope[i].name === "arguments") {
            shadowed = true;
            break;
          }
        if (!shadowed) {
          n.type = ARGUMENTS;
          n.arguments = innerscope;//hack: innerscope is params (maybe extended)
          n[0] = n[1];
          n.splice(1, 1);
          // undo the changes made for INDEX nodes only in fixExp
          if (n[0].type === STRING && propIsNumeric(n[0].value)) {
            n[0].type = NUMBER;
            n[0].value = n[0].value.slice(0, -1) - 0;
          }
        }
      }
    }
    _recurTag(n, innerscope, otherscopes);
  }

  function _recurTag(n, innerscope, otherscopes) {
    n.forEach(function(rand) { 
      tagVarRefsExp[opArity[rand.type]](rand, innerscope, otherscopes); 
    });
  }

  function _call(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n[0].type]](n[0], innerscope, otherscopes);
    n[1].forEach(function(arg) {
      tagVarRefsExp[opArity[arg.type]](arg, innerscope, otherscopes);
    });
  }

  function _nullary(n, innerscope, otherscopes) {
    if (n.type !== IDENTIFIER) return; 
    var boundvar, varname = n.name;
    // search var in innermost scope
    for (var i = innerscope.length - 1; i >= 0; i--) {
      boundvar = innerscope[i];
      if (boundvar.name === varname) {
        //print("stack ref: " + varname);
        n.kind = STACK;
        // if boundvar is a heap var and some of its heap refs get mutated,
        // we may need to update bindings in frames during the cfa.
        n.addr = boundvar.addr; 
        return;
      }
    }
    // search var in other scopes
    for (var i = otherscopes.length - 1; i >= 0; i--) {
      boundvar = otherscopes[i];
      if (boundvar.name === varname) {
        // print("heap ref: " + varname);
        n.kind = boundvar.kind = HEAP;
        n.addr = boundvar.addr;
        flags[boundvar.addr] = true;
        return;
      }
    }
    // var has no binder in the program
    if (commonJSmode && varname === "exports") {
      n.kind = HEAP;
      n.addr = exports_object_av_addr;
      var p = arguments[3]; // exported property name passed as extra arg
      if (p.type === IDENTIFIER)
        exports_object.lines[p.name] = p.lineno;
      return;
    }
    //print("global: " + varname + " :: " + n.lineno);
    n.type = DOT;
    var nthis = idNode({}, "global object");
    nthis.kind = HEAP;
    nthis.addr = global_object_av_addr;
    n.push(nthis);
    n.push(idNode({}, n.name + "-"));
  }

  function _obj_init(n, innerscope, otherscopes) {
    // don't classify property names
    n.forEach(function(prop) {
      if (prop.type !== GETTER && prop.type !== SETTER)
        tagVarRefsExp[opArity[prop[1].type]](prop[1], innerscope, otherscopes);
    });
  }

  function _fun(n, innerscope, otherscopes) {
    var fn = n.fname, len, params = n.params;
    len = otherscopes.length;
    // extend otherscopes
    Array.prototype.push.apply(otherscopes, innerscope); 
    // fun name is visible in the body & not a heap ref, add it to scope
    params.push(fn);
    tagVarRefsStm[n.body.type](n.body, params, otherscopes);
    params.pop();
    if (fn.kind !== HEAP) fn.kind = STACK;    
    params.forEach(function(p) {if (p.kind !== HEAP) p.kind=STACK;});
    // trim otherscopes
    otherscopes.splice(len, innerscope.length);
  }

  tagVarRefsExp[UNARY] = _recurTag;
  tagVarRefsExp[BINARY] = _binary;
  tagVarRefsExp[TERNARY] = _recurTag;
  tagVarRefsExp[MULTI] = _recurTag;
  tagVarRefsExp[MULTI_CALL] = _call;
  tagVarRefsExp[NULLARY] = _nullary;
  tagVarRefsExp[MULTI_OI] = _obj_init;
  tagVarRefsExp[FUN] = _fun;
})();

// jump table for tagging variable references
var tagVarRefsStm = [];

(function() {

  function _fun(n, innerscope, otherscopes) {
    tagVarRefsExp[FUN](n, innerscope, otherscopes);
  }

  function _script(n, innerscope, otherscopes) {
    var i, j, len, vdecl, vdecls = n.varDecls, fdecl, fdecls = n.funDecls;
    // extend inner scope
    j = innerscope.length;
    Array.prototype.push.apply(innerscope, vdecls);
    fdecls.forEach(function(fd) { innerscope.push(fd.fname); });
    // tag refs in fun decls
    fdecls.forEach(function(fd) { 
      tagVarRefsStm[fd.type](fd, innerscope, otherscopes);
    });
    // tag the var refs in the body
    var as = arguments;
    n.forEach(function(stm) { 
      tagVarRefsStm[stm.type](stm, innerscope, otherscopes);
    });
    // tag formals
    vdecls.forEach(function(vd) {
      // for toplevel vars, assigning flags causes the Aval`s to be recorded
      // in the heap. After the analysis, we use that for ctags.
      if (as[3] === "toplevel") flags[vd.addr] = true;
      if (vd.kind !== HEAP) vd.kind = STACK;
    });
    fdecls.forEach(function(fd) { if (fd.kind !== HEAP) fd.kind = STACK; });    
    //trim inner scope 
    innerscope.splice(j, vdecls.length + fdecls.length); 
  }

  function _block(n, innerscope, otherscopes) {
    n.forEach(function(stm) { 
      tagVarRefsStm[stm.type](stm, innerscope, otherscopes);
    });
  }

  function _semi(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.expression.type]](n.expression, 
                                              innerscope, otherscopes);
  }

  function _if(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.condition.type]](n.condition, 
                                             innerscope, otherscopes);
    tagVarRefsStm[n.thenPart.type](n.thenPart, innerscope, otherscopes);
    n.elsePart && 
      tagVarRefsStm[n.elsePart.type](n.elsePart, innerscope, otherscopes);
  }

  function _switch(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.discriminant.type]](n.discriminant, 
                                                innerscope, otherscopes);
    n.cases.forEach(function(branch) {
      branch.caseLabel && 
        tagVarRefsExp[opArity[branch.caseLabel.type]](branch.caseLabel,
                                                      innerscope, otherscopes);
      tagVarRefsStm[branch.statements.type](branch.statements,
                                            innerscope, otherscopes);
    });
  }

  function _for(n, innerscope, otherscopes) {
    n.setup && tagVarRefsExp[opArity[n.setup.type]](n.setup, innerscope, 
                                                    otherscopes);
    n.condition && 
      tagVarRefsExp[opArity[n.condition.type]](n.condition, innerscope, 
                                               otherscopes);
    n.update && tagVarRefsExp[opArity[n.update.type]](n.update, innerscope, 
                                                      otherscopes);
    tagVarRefsStm[n.body.type](n.body, innerscope, otherscopes);
  }

  function _for_in(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.iterator.type]](n.iterator, innerscope,otherscopes);
    tagVarRefsExp[opArity[n.object.type]](n.object, innerscope, otherscopes);
    tagVarRefsStm[n.body.type](n.body, innerscope, otherscopes);
  }

  function _while_do(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.condition.type]](n.condition, innerscope, 
                                             otherscopes);
    tagVarRefsStm[n.body.type](n.body, innerscope, otherscopes);
  }

  function _try(n, innerscope, otherscopes) {
    tagVarRefsStm[n.tryBlock.type](n.tryBlock, innerscope, otherscopes);
    n.catchClauses.forEach(function(clause) {
      var xv = clause.exvar;
      innerscope.push(xv);
      clause.guard && 
        tagVarRefsExp[opArity[clause.guard.type]](clause.guard, innerscope, 
                                                  otherscopes);
      tagVarRefsStm[clause.block.type](clause.block, innerscope, otherscopes);
      innerscope.pop();
      if (xv.kind !== HEAP) xv.kind = STACK;
    });
    n.finallyBlock && 
      tagVarRefsStm[n.finallyBlock.type](n.finallyBlock, 
                                         innerscope, otherscopes);
  }

  function _throw(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.exception.type]](n.exception, innerscope, 
                                             otherscopes);
  }

  function _ret(n, innerscope, otherscopes) {
    tagVarRefsExp[opArity[n.value.type]](n.value, innerscope, otherscopes);
  }
  
  function _with(n, innerscope, otherscopes) {
    throw errorWithCode(UNHANDLED_CONSTRUCT, 
                        "tagVarRefsStm: WITH not implemented");
  }

  tagVarRefsStm[FUNCTION] = _fun;
  tagVarRefsStm[SCRIPT] = _script;
  tagVarRefsStm[BLOCK] = _block;
  tagVarRefsStm[SEMICOLON] = _semi;
  tagVarRefsStm[IF] = _if;
  tagVarRefsStm[SWITCH] = _switch;
  tagVarRefsStm[FOR] = _for;
  tagVarRefsStm[FOR_IN] = _for_in;
  tagVarRefsStm[WHILE] = _while_do;
  tagVarRefsStm[DO] = _while_do;
  tagVarRefsStm[TRY] = _try;
  tagVarRefsStm[THROW] = _throw;
  tagVarRefsStm[RETURN] = _ret;
  tagVarRefsStm[WITH] = _with;
})();


// node, node, node -> undefined
// For every node N in the AST, add refs from N to the node that is normally 
// exec'd after N and to the node that is exec'd if N throws an exception.
function markConts(n, kreg, kexc) {
  var i, len;

  // find functions in expression context and mark their continuations
  function markContsExp(n) {
    switch (opArity[n.type]) {

    case UNARY: case BINARY: case TERNARY: case MULTI:
      n.forEach(markContsExp);
      return;

    case MULTI_CALL:
      markContsExp(n[0]);
      n[1].forEach(markContsExp);
      return;

    case NULLARY: return;

    case FUN:
      markConts(n.body, undefined, undefined);
      return;

    case MULTI_OI:
      n.forEach(function(prop) {
        if (prop.type !== GETTER && prop.type !== SETTER)
          markContsExp(prop[1]);
      });
      return;
    }
  }

  function markContsCase(n, kreg, kexc) {
    var clabel = n.caseLabel, clabelStm, stms = n.statements;
    n.kexc = kexc;
    if (clabel) {
      clabelStm = semiNode(clabel);
      n.kreg = clabelStm;
      markConts(clabelStm, stms, kexc);
    }
    else {
      n.kreg = stms;
    }
    markConts(stms, kreg, kexc);
  }

  function markContsCatch(n, knocatch, kreg, kexc) {
    var guard = n.guard, guardStm, block = n.block;
    if (guard) {// Mozilla catch
      // The guard is of the form (var if expr).
      // If expr is truthy, the catch body is run w/ var bound to the exception.
      // If expr is falsy, we go to the next block (another catch or finally).
      // If the guard or the body throw, the next catches (if any) can't handle
      // the exception, we go to the finally block (if any) directly.      
      markContsExp(guard);
      guardStm = semiNode(guard);
      n.kreg = guardStm;
      guardStm.kcatch = block; // this catch handles the exception
      guardStm.knocatch = knocatch; // this catch doesn't handle the exception
      guardStm.kexc = kexc; // the guard throws a new exception
    }
    markConts(block, kreg, kexc);
  }
  
  switch (n.type) {
  case SCRIPT:
    n.funDecls.forEach(function(fd){markConts(fd.body, undefined, undefined);});
    // fall thru
  case BLOCK:
    n.kexc = kexc;
    len = n.length;
    if (len === 0) 
      n.kreg = kreg;
    else {
      n.kreg = n[0];
      len--;
      for (i=0; i < len; i++) markConts(n[i], n[i+1], kexc);
      markConts(n[len], kreg, kexc);
    }
    return;

  case FUNCTION:
    markConts(n.body, undefined, undefined);
    return;

  case SEMICOLON:
    n.kreg = kreg;
    n.kexc = kexc;
    markContsExp(n.expression);
    return;

    // normally, return & throw don't use their kreg. But this analysis allows 
    // more permissive control flow, to be faster.
  case THROW: 
    n.kreg = kreg;
    n.kexc = kexc;
    markContsExp(n.exception);
    return;

  case RETURN:
    n.kreg = kreg;
    n.kexc = kexc;
    markContsExp(n.value);
    return;

  case IF:
    var thenp = n.thenPart, elsep = n.elsePart, condStm;
    condStm = semiNode(n.condition);
    n.kreg = condStm; // first run the test
    n.kexc = kexc;
    markConts(condStm, thenp, kexc); // ignore result & run the true branch
    markConts(thenp, elsep || kreg, kexc); // then run the false branch
    elsep && markConts(elsep, kreg, kexc);
    return;
        
  case SWITCH:
    var cases = n.cases, discStm;
    discStm = semiNode(n.discriminant);
    n.kreg = discStm; // first run the discriminant, then all branches in order
    n.kexc = kexc;
    markConts(discStm, cases[0], kexc);
    for (i = 0, len = cases.length - 1; i < len; i++) //no empty switch, len >=0
      markContsCase(cases[i], cases[i+1], kexc);
    markContsCase(cases[len], kreg, kexc);
    return;

  case FOR: 
    var body = n.body;
    n.kexc = kexc;
    // Do setup, condition, body & update once.
    var setup = n.setup, setupStm, condition = n.condition, condStm;
    var update = n.update, updStm;
    n.kexc = kexc;
    if (!setup && !condition)
      n.kreg = body;
    else if (setup && !condition) {
      setupStm = semiNode(setup);
      n.kreg = setupStm;
      markConts(setupStm, body, kexc);
    }
    else {// condition exists
      condStm = semiNode(condition);
      markConts(condStm, body, kexc);
      if (setup) {
        setupStm = semiNode(setup);
        n.kreg = setupStm;
        markConts(setupStm, condStm, kexc);  
      }
      else n.kreg = condStm;
    }
    if (update) {
      updStm = semiNode(update);
      markConts(body, updStm, kexc);
      markConts(updStm, kreg, kexc);
    }
    else markConts(body, kreg, kexc);
    return;

  case FOR_IN:
    var body = n.body;
    n.kexc = kexc;
    n.kreg = body;
    markConts(body, kreg, kexc);
    return;

  case WHILE:
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = condStm;
    n.kexc = kexc;
    markConts(condStm, body, kexc);
    markConts(body, kreg, kexc);
    return;

  case DO:
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = body;
    n.kexc = kexc;
    markConts(body, condStm, kexc);
    markConts(condStm, kreg, kexc);
    return;

  case TRY:
    var fin = n.finallyBlock, clause, clauses = n.catchClauses, knocatch;
    // process back-to-front to avoid if-madness
    if (fin) {
      markConts(fin, kreg, kexc);
      knocatch = kexc = kreg = fin; // TRY & CATCHes go to fin no matter what
    }
    for (len = clauses.length, i = len-1; i>=0; i--) {
      clause = clauses[i];
      markContsCatch(clause, knocatch, kreg, kexc);
      knocatch = clause;
    }
    markConts(n.tryBlock, kreg, knocatch || kexc);
    n.kreg = n.tryBlock;
    return;

  default:
    throw errorWithCode(UNHANDLED_CONSTRUCT, "markConts: unknown case");
  }
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////   CFA2  code  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

var uprot, uprotNew, uvar;

// abstract objects and abstract values are different!!!

var heap;
// modified[addr] is a timestamp that shows the last time heap[addr] was updated
var modified; 
var timestamp;
// counts the number of pending calls to evalFun
var depth;
// flags is an array with two kinds of stuff. 
// If i is the addr of a fun node n, flags[i] points to n.
// If i is the addr of a var, flags[i] is true if the var is a heap var.
var flags;
var exports_object;
var exports_object_av_addr;
var commonJSmode;

// A summary contains a function node (fn), an array of abstract values (args),
// a timestamp (ts) and an abstract value (res). It means: when we call fn w/ 
// args and the heap's timestamp is ts, we get back res.

// summaries: a map from addresses of fun nodes to triples {ts, insouts, type},
// where ts is a timestamp, insouts is an array of args-result pairs,
// and type is the join of all args-result pairs.
var summaries;

// pending: a map from addresses of fun nodes to pairs {ts, ins}, where ts is a
// timestamp, and ins is an array of [args, boolean] arrays.

// pending is used to hold some info that exists in the runtime stack. For each
// call to evalFun that hasn't returned, pending contains a quadruple [a,t,d,b]
// where a is the args for the call, t is the timestamp at the time of the call,
// d is the stack depth (how many calls to evalFun are pending) and b is a 
// boolean used for recursive functions.
var pending;

// when initGlobals is called, count has its final value (core objs are in heap)
// FIXME, I'm violating the invariant in "function cfa2". Change it?
function initGlobals() {
  uprot = uprotNew = uvar = 0;
  big_ts = 1000;
  rethrows = 0;
  callsEvalFun = 0;
  noSum = 0;
  maxBucketSize = 0;
  aveq_lens = buildArray(10, 0);
  // the vars above are used only when debugging

  timestamp = 0;
  heap = new Array(count); // reserve heap space, don't grow it gradually
  modified = buildArray(count, timestamp);
  depth = 0;
  summaries = {}; // We use {} instead of an Array b/c it's sparse.
  pending = {};
  flags = buildArray(count);
  exports_object = {lines : {}};
}

// string -> void
// works only in NodeJS 
function dumpHeap(filename) {
  var fs = require("fs"), fd = fs.openSync(filename, "w", mode=0777);
  for (var i = 0, l = heap.length; i < l; i++)
    fs.writeSync(fd,
                 "[" + i + "]\n" + (heap[i] ? heap[i].toString(2) : "") + "\n",
                 null,
                 encoding='utf8');
  fs.closeSync(fd);
}

// non-empty array of strings -> void
function normalizeUnionType(types) {
  // any is a supertype of all types
  if (types.member(function(t) { return t === "any";})) {
    types[0] = "any";
    types.length = 1;
  }
  else
    types.rmDups(function(e1, e2) {return e1 === e2;});
}

// Constructor for abstract properties
// Takes an object w/ the property's attributes
// Don't call from outside the abstract-values module, use addProp instead.
function Aprop(attribs){
  this.aval = attribs.aval;
  // writable, enumerable and configurable default to true
  this.write = (attribs.write !== undefined) ? attribs.write : true;
  this.enum = (attribs.enum !== undefined) ? attribs.enum : true;
  this.config = (attribs.config !== undefined) ? attribs.config : true;
}

// optional number -> string
Aprop.prototype.toString = function(indent) {
  return this.aval.toString(indent);
};

// An abstract object o1 is represented as an array object o2. 
// The array elms of o2 are used for special properties of o1 & the properties
// of o2 are used for ordinary properties of o1.
// Can't use Array or Object properties for o2, e.g. if o1 has a "length"
// property then o2 has it and Array.length is shadowed.
// 1st elm: the address of o1's prototype in the heap
// 2nd elm: may contain a function node.
function Aobj(specialProps) {
  this.push(specialProps.proto); /* optional abstract value */
  this.push(specialProps.fun); /* optional function node */
}

Aobj.prototype = new Array();

// Takes an optional array for cycle detection.
Aobj.prototype.toType = function(seenObjs) {
  var self = this;
  if (seenObjs) {
    if (seenObjs.member(function(o) { return o === self; }))
      return "any";
    else
      seenObjs.push(self);
  }
  else
    seenObjs = [self];

  if (this[1]) return funToType(this[1], seenObjs);
  var c = this.getProp("constructor-");
  var types = [];
  if (c === undefined) return "Global Object";
  c.forEachObj(function(o) { if (o[1]) types.push(o[1].fname.name); });
  if (types.length === 0) throw new Error("didn't find a name for constructor");
  normalizeUnionType(types);
  if (types.length === 1) {
    if (types[0] === "Array") return this.toArrayType(seenObjs);
    return types[0];
  }
  return ("<" + types.join(" | ") + ">");
};

// For homogeneous arrays, include the type of their elms.
// Takes an optional array for cycle detection.
Aobj.prototype.toArrayType = function(seenObjs) {
  var elmtype = BOTTOM, self = this;
  this.forEachOwnProp(function(p) {
    if (propIsNumeric(p)) elmtype = avjoin(elmtype, self.getOwnExactProp(p));
  });
  elmtype = elmtype.toType(seenObjs);
  if (/\|/.test(elmtype) || elmtype === "any")
    return "Array";
  else
    return "Array[" + elmtype + "]";
};

// nothing -> function node
Aobj.prototype.getFun = function() { return this[1]; };

// Aval -> undefined
Aobj.prototype.updateProto = function(av) {
  if (this[0]) {
    if (!avlt(av, this[0])) {
      this[0] = avjoin(this[0], av);
      ++timestamp;
      // ++uprot;
    }
    return;
  }
  this[0] = av;
  ++timestamp;
  // ++uprotNew;
};

// string -> boolean
function propIsNumeric(p) {
  return p === "-number" || (/-$/.test(p) && !isNaN(p.slice(0, -1)));
}

// act: Aobj, optional Array[string] -> {val : A, stop : boolean}
// combine: Array[A] -> A
function foldProtoChain(o, act, combine) {
  function recur(o, seenObjs, seenProps) {
    var v = act(o, seenProps), val = v.val;
    if (v.stop) return val; // stop going up the chain
    if (!o[0]) return val; // reached the end of the prototype chain
    if (seenObjs.member(function(o2) { return o === o2; }))
      return val;
    else
      seenObjs.push(o);
    var a = [], solen = seenObjs.length, splen = seenProps.length;
    o[0].forEachObj(function(proto) {
      a.push(recur(proto, seenObjs, seenProps));
      seenObjs.splice(solen, seenObjs.length);
      seenProps.splice(splen, seenProps.length);
    });
    a.push(val); // The current level's result is last, 'combine' pops to get it
    return combine(a);
  }

  return recur(o, [], []);
}

// string -> Aval or undefined
// doesn't look in prototype chain
Aobj.prototype.getOwnExactProp = function(pname) {
  return this[pname] && this[pname].aval;
};

// string -> Aval or undefined
// doesn't look in prototype chain
// pname is not "-number" or "-string"
Aobj.prototype.getOwnProp = function(pname) {
  if (this.hasOwnProperty(pname)) 
    return this[pname].aval;
  if (this.numPropsMerged && propIsNumeric(pname))
    return this["-number"].aval;
  if (this.strPropsMerged) 
    return this["-string"].aval;
};

// string -> Aval or undefined
// May include "-number" and "-string" in its result
Aobj.prototype.getProp = function(pname) {
  return getProp(this, pname, true);
};

// Aobj, string, boolean -> Aval or undefined
// pname is not "-number" or "-string"
// Looks in prototype chain. Returns undefined iff the property doesn't exist in
// *all* paths up the prototype chain o/w it returns an Aval.
function getProp(o, pname, lax) {
  function act(o) {
    if (o.hasOwnProperty(pname))
      return {val : o[pname].aval, stop : true};
    if (lax && o.numPropsMerged) {
      if (propIsNumeric(pname))
        return {val : o["-number"].aval, stop : true};
      if (o.strPropsMerged)
        return {val : o["-string"].aval, stop : false};
    }
    return {val : undefined, stop : false};
  }

  function combine(avs) {
    var notfoundinsomechain = false, val = avs.pop();
    avs.forEach(function(av) {
      if (!av)
        notfoundinsomechain = true;
      else
        val = maybeavjoin(val, av);
    });
    return val && (notfoundinsomechain ? avjoin(AUNDEF, val) : val);
  }
  return foldProtoChain(o, act, combine);
}

Aobj.prototype.getNumProps = function() {
  this.mergeNumProps();
  return this["-number"].aval;
};

Aobj.prototype.getStrProps = function() {
  function act(o, seenProps) {
    if (o.strPropsMerged)
      return {val : o["-string"].aval, stop : false};
    var val = BOTTOM;
    o.forEachOwnProp(function(pname, pval) {
      if (pval.enum && !seenProps.member(function(p) { return p === pname; })) {
        val = avjoin(val, o[pname].aval);
        (pname !== "-number") && seenProps.push(pname);
      }
    });
    return {val : val, stop : false};
  }

  function combine(avs) {
    var val = BOTTOM;
    avs.forEach(function(av) { val = avjoin(val, av); });
    return val;
  }
  return foldProtoChain(this, act, combine);
};

// string, Object -> undefined
// attribs.aval is the property's value
// The property shouldn't be already present, it'll be overwritten
Aobj.prototype.addProp = function(prop, attribs) {
  this[prop] = new Aprop(attribs);
};

// string, Aval -> undefined
Aobj.prototype.updateExactProp = function(pname, newv) {
  if (this.hasOwnProperty(pname)) {
    var p = this[pname];
    if (!avlt(newv, p.aval)) {
      p.aval = avjoin(p.aval, newv);
      ++timestamp;
    }
    return;
  }
  this[pname] = new Aprop({aval : newv});
  ++timestamp;
};

// string, Aval -> undefined
// pname is not "-number" or "-string"
Aobj.prototype.updateProp = function(pname, newv) {
  function upd(pname, pval, newv) {
    if (!avlt(newv, pval.aval)) {
      pval.aval = avjoin(pval.aval, newv);
      ++timestamp;
    }
  }

  if (this.hasOwnProperty(pname))
    // either it's not enumerable, or it doesn't interfere with "-number"
    upd(pname, this[pname], newv);
  else {// the new property is enumerable
    if (this.strPropsMerged)
      upd("-string", this["-string"], newv);
    if (this.numPropsMerged && propIsNumeric(pname))
      upd("-number", this["-number"], newv);
    else if (!this.strPropsMerged) {
      this[pname] = new Aprop({aval : newv});
      ++timestamp;
    }
  }
};

// Aval -> undefined
Aobj.prototype.updateNumProps = function(newv) {
  this.mergeNumProps();
  this.updateExactProp("-number", newv);
};

// Aval -> undefined
Aobj.prototype.updateStrProps = function(newv) {
  this.mergeStrProps();
  this.updateExactProp("-number", newv);
  this.updateExactProp("-string", newv);
};

// merge all numeric properties of the object to one generic number property
Aobj.prototype.mergeNumProps = function() {
  if (this.numPropsMerged) return;
  var av = BOTTOM, self = this;
  this.forEachOwnProp(function(p) {
    if (propIsNumeric(p)) {
      av = avjoin(av, self[p].aval);
      delete self[p]; // don't keep a mix of merged and unmerged properties.
    }
  });
  this.updateExactProp("-number", av); // this bumps timestamp, don't bump again
  this.numPropsMerged = true;
};

Aobj.prototype.mergeStrProps = function() {
  if (this.strPropsMerged) return;
  if (!this.numPropsMerged) this.mergeNumProps();
  var av = BOTTOM, self = this;
  this.forEachOwnProp(function(pname, pval) {
    if (pval.enum) {
      av = avjoin(av, pval.aval);
      if (pname !== "-number") delete self[pname];
    }
  });
  this.updateExactProp("-string", av); // this bumps timestamp, don't bump again
  this.strPropsMerged = true;
};

Aobj.prototype.forEachOwnProp = function(f) {
  for (var p in this)
    if (this[p] instanceof Aprop) 
      f(p, this[p]); // f may ignore its second argument
};

Aobj.prototype.forEachEnumProp = function(f) {
  function act(o, seenProps) {
    for (var p in o) {
      var pval = o[p];
      if ((pval instanceof Aprop) && pval.enum
          && !seenProps.member(function(pname) { return p === pname; })) {
        f(p, pval.aval); // f may ignore its second argument
        seenProps.push(p);
      }
    }
    return {val:undefined, stop:false};
  }
  foldProtoChain(this, act, function() {});
};

// optional number -> string
// Returns a multiline string, each line starts with indent (or more) spaces
Aobj.prototype.toString = function(indent) {
  indent = indent || 0;
  var i1 = buildString(indent, " "), i2 = i1 + "  ";

  var s = i1 + "<proto>:\n";
  s += (this[0] ? this[0].toString(indent + 2) : (i2 + "??\n"));
  
  if (this[1]) {
    s += i1 + "<function>:\n" + i2 + this[1].fname.name +
      (this[1].lineno ? ("@" + this[1].lineno) : "") + "\n";
  }

  var self = this;
  this.forEachOwnProp(function(p) {
    var pname = p;
    if (p !== "-number" && p !== "-string")
      pname = p.slice(0, -1);
    s += i1 + pname + ":\n" + self[p].toString(indent + 2);
  });

  return s;
};


// An abstract value is an obj w/ 2 properties: base is a number whose bits
// encode the base values, objs is an array of sorted heap addresses that 
// denotes a set of objects.
const ANUM = makeBaseAval(1), ASTR = makeBaseAval(2), ABOOL = makeBaseAval(4);
const BOTTOM=makeBaseAval(0), AUNDEF=makeBaseAval(8), ANULL=makeBaseAval(16);
const RESTARGS = -1;
const INVALID_TIMESTAMP = -1;

// AUNDEF and ANULL are the only abstract vals that contain just falsy concrete
// vals guaranteed. All others may contain both truthy & falsy concrete vals.

// constructor for abstract values. Should only be called from the wrappers.
function Aval() {}

// number -> Aval
function makeBaseAval(base) {
  var v = new Aval();
  v.base = base;
  v.objs = [];
  return v;
}

// number -> Aval
// When creating an abs. value, it can contain at most one object
function makeObjAval(objaddr) {
  var v = new Aval();
  v.base = 0;
  v.objs = [objaddr];
  return v;
}

// string -> Aval
function makeStrLitAval(s) {
  var v = new Aval();
  v.base = 2;
  v.objs = [];
  v.str = s;
  return v;
}

// used by parts of the code that don't know the representation of Aval
Aval.prototype.getBase = function() { return makeBaseAval(this.base); };

// nothing -> string or undefined
Aval.prototype.getStrLit = function() { return this.str; };

// Takes an optional array for cycle detection.
Aval.prototype.toType = function(seenObjs) {
  var i = 1, base = this.base, types = [];
  var basetypes = {1 : "number", 2 : "string", 4 : "boolean",
                   8 : "undefined", 16 : "null"};
  while (i <= 16) {
    if ((base & i) === i) types.push(basetypes[i]);
    i *= 2;
  }
  // If uncommented, tags show string constants where possible.
  // if ((base & 2) && (this.str !== undefined)) {
  //   types.rmElmAfterIndex(function(s) {return s === "string";}, 0);
  //   types.push("\"" + this.str + "\"");
  // }
  seenObjs || (seenObjs = []);
  var slen = seenObjs.length;
  this.forEachObj(function (o) {
    types.push(o.toType(seenObjs));
    seenObjs.splice(slen, seenObjs.length);
  });
  if (types.length === 0) return "any";
  normalizeUnionType(types);
  if (types.length === 1) return types[0];
  return ("<" + types.join(" | ") + ">");
};

// nothing -> Aval
// Used when scalars need to be converted to objects
Aval.prototype.baseToObj = function() {
  var base = this.base;
  if (base & 7 === 0) return this;
  var av = makeBaseAval(0);
  av.objs = this.objs;
  if (base & 2) av = avjoin(av, generic_string_av);
  if (base & 1) av = avjoin(av, generic_number_av);
  if (base & 4) av = avjoin(av, generic_boolean_av);
  return av;
};

// fun takes an Aobj
Aval.prototype.forEachObj = function(fun) {
  var objaddrs = this.objs;
  if (objaddrs.length === 1) // make common case faster
    fun(heap[objaddrs[0]]);
  else
    objaddrs.forEach(function(addr) { fun(heap[addr]); });
};

// string -> Aval
Aval.prototype.getProp = function(pname) {
  var av = BOTTOM;
  this.forEachObj(function(o) { av = avjoin(av, o.getProp(pname) || AUNDEF); });
  return av;
};

// string, Aval -> undefined
Aval.prototype.updateProp = function(pname, av) {
  this.forEachObj(function(o) { o.updateProp(pname, av); });
};

// array of Aval, node -> Ans
// Call each function with args. args[0] is what THIS is bound to.
// FIXME: record error if rator contains base vals and non-functions
Aval.prototype.callFun = function(args, callNode) {
  var retval = BOTTOM, errval, ans, debugCalls = 0;
  this.baseToObj().forEachObj(function(o) {
    var clos = o.getFun();
    if (!clos) return;
    debugCalls++;
    ans = evalFun(clos, args, false, callNode);
    retval = avjoin(retval, ans.v);
    errval = maybeavjoin(errval, ans.err);
  });

  // var ratorNode = callNode && callNode[0];
  // if (!debugCalls) {
  //   var funName, ln = ratorNode.lineno;
  //   switch (ratorNode.type) {
  //   case IDENTIFIER:
  //     funName = ratorNode.name;
  //     break;
  //   case FUNCTION:
  //     funName = ratorNode.fname.name;
  //     break;
  //   case DOT:
  //     if (ratorNode[1].type === IDENTIFIER) {
  //       funName = ratorNode[1].name.slice(0, -1);
  //       break;
  //     }
  //     // fall thru
  //   default:
  //     funName = "??";
  //     break;
  //   }
  //   if (args[0] === global_object_av)
  //     print("unknown function: " + funName + ", line " + (ln || "??"));
  //   else
  //     print("unknown method: " + funName + ", line " + (ln || "??"));
  // }
  
  return new Ans(retval, undefined, errval);
};

Aval.prototype.hasNum = function() { return this.base & 1; };

Aval.prototype.hasStr = function() { return this.base & 2; };

// returns true if it can guarantee that the Aval is falsy.
Aval.prototype.isFalsy = function() {
  var base = this.base;
  return this.objs.length === 0 && base !== 0 && 
    (base % 8 === 0 || (base === 2 && this.str === "-"));
};

// returns true if it can guarantee that the Aval is truthy.
Aval.prototype.isTruthy = function() {
  var base = this.base;
  return (this.objs.length === 0 && base === 2 && this.str !== "-");
};

// silly hashing function
Aval.prototype.hash = function() {
  if (this.base) return this.base % 9;
  var objs = this.objs;
  return (objs[0] + (objs[1] << 1) + (objs[2] << 2)) % 9;
};

// optional number -> string
Aval.prototype.toString = function(indent) {
  var i1 = buildString(indent || 0, " ");
  var i = 1, base = this.base, types = [];
  var basetypes = {1 : "number", 2 : "string", 4 : "boolean",
                   8 : "undefined", 16 : "null"};
  while (i <= 16) {
    if ((base & i) === i) types.push(basetypes[i]);
    i *= 2;
  }
  return (i1 + "Base: " + types.join(", ") + "\n" +
          i1 + "Objects: " + this.objs.join(", ") + "\n");
};

// Aval, Aval -> Aval
function avjoin(v1, v2) {
  var os1 = v1.objs, os1l = os1.length, os2 = v2.objs, os2l = os2.length;
  var b1 = v1.base, b2 = v2.base, av = makeBaseAval(b1 | b2);

  if (av.base & 2) {
    if (b1 & 2) {
      if (!(b2 & 2) || v1.str === v2.str)
        av.str = v1.str;
    }
    else // (b2 & 2) is truthy
      av.str = v2.str;
  }

  if (os1l === 0)
    av.objs = os2; // need a copy of os2 here? I think not.
  else if (os2l === 0)
    av.objs = os1; // need a copy of os1 here? I think not.
  else if (os1 === os2)
    av.objs = os1;
  else if (os1l === os2l) {
    for (var i = 0; i < os1l; i++) if (os1[i] !== os2[i]) break;
    if (i === os1l) {
      av.objs = v2.objs = os1;
      return av;
    }
    else
      av.objs = arraymerge(os1, os2);
  }
  else // merge the two arrays
    av.objs = arraymerge(os1, os2);
  return av;
}

// Aval or undefined, Aval or undefined -> Aval or undefined
function maybeavjoin(v1, v2) {
  if (!v1) return v2;
  if (!v2) return v1;
  return avjoin(v1, v2);
}

// Helps track if there is enough sharing of big abstract values in the heap.
// var aveq_lens;

// Aval, Aval -> boolean
// compares abstract values for equality
function aveq(v1, v2) {
  if (v1.base !== v2.base) return false;
  if (v1.str !== v2.str) return false;
  var os1 = v1.objs, os2 = v2.objs, len = os1.length, i; 
  if (len !== os2.length) return false;
  if (os1 === os2) return true;
  //aveq_lens[len]++;
  for (i=0; i<len; i++) if (os1[i] !== os2[i]) return false;
  return true;
}

// Aval, Aval -> boolean
// returns true if v1 is less than v2
function avlt(v1, v2) {
  var b1 = v1.base, b2 = v2.base;
  if (b1 > (b1 & b2)) return false;
  if ((b1 & 2) && v2.str !== undefined && v2.str !== v1.str)
    return false;
  var os1 = v1.objs, os1l = os1.length, os2 = v2.objs, os2l = os2.length;
  if (os1l === 0 || os1 === os2) return true;
  if (os1l > os2l) return false;
  for (var i = 0, j = 0; i < os1l; i++) {
    while (os2[j] < os1[i]) j++;
    if (j === os2l || os1[i] !== os2[j])
      return false; // there's an elm is os1 that's not in os2
  }
  return true;
}

// function node -> Aval
// If the program doesn't set a function's prototype property, create default.
function makeDefaultProto(n) {
  var o = new Aobj({proto:object_prototype_av});
  o["constructor-"] = new Aprop({aval:makeObjAval(n.addr), enum:false});
  var paddr = n.defaultProtoAddr;
  heap[paddr] = o;
  return makeObjAval(paddr);
}

// heap address, Aval -> undefined
function updateHeapAv(addr, newv) {
  var oldv = heap[addr]; //oldv shouldn't be undefined
  if (!avlt(newv, oldv)) {
    heap[addr] = avjoin(oldv, newv);
    modified[addr] = ++timestamp;
    // ++uvar;
  }
}

// abstract plus
function aplus(v1, v2) {
  if (v1.objs.length !== 0 || v2.objs.length !== 0)
    return makeBaseAval(3);
  var base = ((v1.base | v2.base) & 2); // base is 0 or 2
  if ((v1.base & 29) !== 0 && (v2.base & 29) !== 0) base |= 1;
  return makeBaseAval(base);
}

// Invariant: the following code should know nothing about the representation 
// of abstract values.

////////////////////////////////////////////////////////////////////////////////
/////////////////////  CORE AND CLIENT-SIDE OBJECTS   //////////////////////////
////////////////////////////////////////////////////////////////////////////////

var global_object_av;
var global_object_av_addr;
var object_prototype_av;
var function_prototype_av;
var array_constructor;
var regexp_constructor;
// Used to automatically convert base values to objs and call methods on them
var generic_number_av;
var generic_string_av;
var generic_boolean_av;

// string, function, number -> function node
function funToNode(name, code, arity) {
  var n = new Node({}, FUNCTION);
  n.fname = idNode({}, name);
  n.builtin = true;
  // built-in funs have no params property but they have an arity property
  // instead. It's only used by the apply method.
  n.arity = arity;
  n.body = code;
  return n;
}

// Aobj, string, function, number -> undefined
function attachMethod(o, mname, mcode, arity) {
  var foaddr = ++count;
  heap[foaddr] = new Aobj({proto : function_prototype_av,
                           fun : funToNode(mname, mcode, arity)});
  o.addProp(mname + "-",  {aval : makeObjAval(foaddr), enum : false});
}

// create the JS core objects in heap & fill in core
function initCoreObjs() {

  function toStr(args) { return new Ans(ASTR); }
  function toNum(args) { return new Ans(ANUM); }
  function toBool(args) { return new Ans(ABOOL); }
  function toThis(args) { return new Ans(args[0]); }

  // Global object
  var go = new Aobj({}), goaddr = ++count;
  var goav = makeObjAval(goaddr), goavaddr = ++count;
  global_object_av = goav;
  heap[goaddr] = go;
  heap[goavaddr] = goav;
  global_object_av_addr = goavaddr;
  
  // global identifiers and methods
  go.addProp("Infinity-", {aval:ANUM, write:false, enum:false, config:false});
  go.addProp("NaN-", {aval:ANUM, write:false, enum:false, config:false});
  go.addProp("undefined-",{aval:AUNDEF, write:false, enum:false, config:false});

  // Object.prototype
  var op = new Aobj({}), opaddr = ++count, opav = makeObjAval(opaddr);
  object_prototype_av = opav;
  heap[opaddr] = op;

  // Object.__proto__ (same as Function.prototype)
  var o_p = new Aobj({proto:opav}), o_paddr = ++count;
  var o_pav = makeObjAval(o_paddr);
  function_prototype_av = o_pav;
  heap[o_paddr] = o_p;

  // Function.prototype.prototype
  var fpp = new Aobj({proto : opav}), fppaddr = ++count;
  var fppav = makeObjAval(fppaddr);
  heap[fppaddr] = fpp;
  o_p.addProp("prototype-", {aval : fppav, enum : false, config : false});
  fpp.addProp("constructor-", {aval : o_pav, enum : false});

  // Object
  var _Object = (function () {
    // nonew is used when Object is called w/out new 
    var nonew = new Aobj({proto : opav}), nonewaddr = ++count;
    var nonewav = makeObjAval(nonewaddr);
    heap[nonewaddr] = nonew;

    return function (args, withNew) {
      var retval = withNew ? args[0] : nonewav;
      var arg = args[1];
      if (!arg) {
        retval.forEachObj(function (o) { o.updateProto(opav); });
        return new Ans(retval);
      }
      else {
        // throw errorWithCode(CFA_ERROR, "call a suitable constructor, " +
        //                     "hasn't been defined yet. FIXME");
        retval.forEachObj(function (o) { o.updateProto(opav); });
        return new Ans(retval);
      }
    };
  })();
  var o = new Aobj({proto : o_pav, fun : funToNode("Object", _Object)});
  var oaddr = ++count, oav = makeObjAval(oaddr);
  heap[oaddr] = o;
  // Object is a heap var that will contain an Aval that points to o
  go.addProp("Object-",{aval : oav, enum : false});
  o.addProp("prototype-", {aval:opav, write:false, enum:false, config:false});
  op.addProp("constructor-", {aval : oav, enum : false});

  // Function
  var f = new Aobj({proto : o_pav}), faddr = ++count;
  var fav = makeObjAval(faddr);
  heap[faddr] = f;
  go.addProp("Function-",{aval : fav, enum : false});
  f.addProp("prototype-", {aval:o_pav, write:false, enum:false, config:false});
  o_p.addProp("constructor-", {aval : fav, enum : false});

  // Methods are attached here because o_pav must be defined already.
  attachMethod(go, "isFinite", toBool, 1);
  attachMethod(go, "isNaN", toBool, 1);
  attachMethod(go, "parseInt", toNum, 1);
  attachMethod(op, "hasOwnProperty", toBool, 1);
  attachMethod(op, "toString", toStr, 0);
  attachMethod(op, "valueOf", toThis, 0);
  attachMethod(o_p, "toString", toStr, 0);
  attachMethod(o_p, "call",
               function(args) {
                 var f = args.shift();
                 args[0] || args.unshift(global_object_av);
                 return f.callFun(args);
               }, 0);
  attachMethod(o_p, "apply",
               function(args) {
                 var recv = args[1] || global_object_av, a2 = args[2], rands,
                 av, maxArity = 0, restargs, i, ans, retval = BOTTOM, errval;
                 // We can't compute the arguments once for all functions that
                 // may be applied. The functions may have different arity which
                 // impacts what goes to the restargs for each function.
                 args[0].forEachObj(function(o) {
                   var clos = o.getFun(), pslen, i;
                   if (!clos) return;
                   if (clos.builtin)
                     pslen = clos.arity;
                   else
                     pslen = clos.params.length;
                   // compute arguments
                   restargs = BOTTOM;
                   rands = buildArray(pslen, BOTTOM);
                   if (a2) { // a2 is the array passed at the call to apply.
                     a2.forEachObj(function(o) {
                       if (o.numPropsMerged) {
                         av = o.getNumProps();
                         restargs = avjoin(restargs, av);
                         for (i = 0; i < pslen; i++)
                           rands[i] = avjoin(rands[i], av);
                       }
                       else {
                         for (i = 0; i < pslen; i++) {
                           av = o.getOwnExactProp(i + "-") || AUNDEF;
                           rands[i] = avjoin(rands[i], av);
                         }
                         while (true) { // search for extra arguments
                           av = o.getOwnExactProp(i++ + "-");
                           // to find the end of the array, we must see that
                           // an elm *definitely* doesn't exist, different
                           // from AUNDEF
                           if (!av) break;
                           restargs = avjoin(restargs, av);
                         }
                       }
                     });
                   }
                   else {
                     rands = buildArray(pslen, BOTTOM);
                   }
                   // do function call
                   rands.unshift(recv);
                   rands.push(restargs);
                   ans = evalFun(clos, rands, false);
                   retval = avjoin(retval, ans.v);
                   errval = maybeavjoin(errval, ans.err);
                 });
                 return new Ans(retval, undefined, errval);
               }, 2);  

  (function () {
    // Array.prototype
    var ap = new Aobj({proto:opav}), apaddr = ++count;
    var apav = makeObjAval(apaddr);
    heap[apaddr] = ap;

    function putelms(args) {
      args[0].forEachObj(function (o) {
        for (var i = 1, len = args.length; i < len; i++)
          o.updateNumProps(args[i]);
      });
      return new Ans(ANUM);
    }

    function getelms(args) {
      var av = BOTTOM, av2;
      args[0].forEachObj(function (o) { av = avjoin(av, o.getNumProps()); });
      return new Ans(av);
    }
    
    attachMethod(ap, "concat",
                 // lose precision by not creating a new array
                 function(args) {
                   var thisarr = args[0], av = BOTTOM;
                   // if arg is base, join it, if it's array join its elms
                   for (var i = 1, l = args.length; i < l; i++) {
                     var avarg = args[i];
                     av = avjoin(av, avarg.getBase());
                     avarg.forEachObj(function(o) {
                       if (/^Array/.test(o.toType()))
                         av = avjoin(av, o.getNumProps());
                     });
                     thisarr.forEachObj(function(o) { o.updateNumProps(av); });
                   }
                   return new Ans(thisarr);
                 }, 0);
    attachMethod(ap, "join", toStr, 1);
    attachMethod(ap, "pop", getelms, 0);
    attachMethod(ap, "push", putelms, 0);
    attachMethod(ap, "slice", toThis, 2);
    attachMethod(ap, "sort", toThis, 1);
    attachMethod(ap, "splice", toThis, 0);
    attachMethod(ap, "shift", getelms, 0);
    attachMethod(ap, "toString", toStr, 0);
    attachMethod(ap, "unshift", putelms, 0);

    // Array
    var _Array = (function () {
      // nonew is used when Array is called w/out new 
      var nonew = new Aobj({proto : apav}), nonewaddr = ++count;
      var nonewav = makeObjAval(nonewaddr);
      heap[nonewaddr] = nonew;

      return function(args, withNew) {
        var retval = withNew ? args[0] : nonewav;
        var arglen = args.length;
        retval.forEachObj(function (o) {
          o.updateProto(apav);
          if (o.getOwnExactProp("length-"))
            o.updateProp("length-", ANUM);
          else
            o.addProp("length-", {aval : ANUM, enum : false});
        });
        if (arglen <= 2) // new Array(), new Array(size)
          ;
        else { // new Array(elm1, ... , elmN)
          retval.forEachObj(function (o) {
            for (var i = 1; i < arglen; i++) 
              o.updateProp((i - 1) + "-", args[i]);
          });
        }
        return new Ans(retval);
      };
    })();
    array_constructor = _Array;
    var a = new Aobj({proto : o_pav, fun : funToNode("Array", _Array)});
    var aaddr = ++count, aav = makeObjAval(aaddr);
    heap[aaddr] = a;
    go.addProp("Array-", {aval : aav, enum : false});
    a.addProp("prototype-", {aval:apav, write:false, enum:false, config:false});
    ap.addProp("constructor-", {aval : aav, enum : false});
  })();

  (function () {
    // Number.prototype
    var np = new Aobj({proto:opav}), npaddr = ++count;
    var npav = makeObjAval(npaddr);
    heap[npaddr] = np;
    attachMethod(np, "toString", toStr, 0);
    attachMethod(np, "valueOf", toNum, 0);
    // create generic number object
    heap[++count] = new Aobj({proto : npav});
    generic_number_av = makeObjAval(count);

    // Number
    function _Number(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(npav); });
        return new Ans(args[0]);
      }
      return new Ans(ANUM);
    }
    var n = new Aobj({proto : o_pav, fun : funToNode("Number", _Number)});
    var naddr = ++count, nav = makeObjAval(naddr);
    heap[naddr] = n;
    go.addProp("Number-",{aval : nav, enum : false});
    n.addProp("prototype-", {aval:npav, write:false, enum:false, config:false});
    np.addProp("constructor-", {aval : nav, enum : false});
  })();

  (function () {
    // String.prototype
    var sp = new Aobj({proto:opav}), spaddr = ++count;
    var spav = makeObjAval(spaddr);
    heap[spaddr] = sp;
    attachMethod(sp, "charAt", toStr, 1);
    attachMethod(sp, "charCodeAt", toNum, 1);
    attachMethod(sp, "indexOf", toNum, 2);
    attachMethod(sp, "lastIndexOf", toNum, 2);
    // all Arrays returned by calls to match are merged in one
    var omatch = new Aobj({}), omatchaddr = ++count;
    var omatchav = avjoin(ANULL, makeObjAval(omatchaddr));
    heap[omatchaddr] = omatch;
    array_constructor([omatchav], true);
    omatch.updateNumProps(ASTR);
    omatch.addProp("index-", {aval : ANUM});
    omatch.addProp("input-", {aval : ASTR});
    attachMethod(sp, "match", function(args) { return new Ans(omatchav); }, 1);
    attachMethod(sp, "replace", toStr, 2);
    attachMethod(sp, "slice", toStr, 2);
    attachMethod(sp, "substr", toStr, 2);
    attachMethod(sp, "substring", toStr, 2);
    attachMethod(sp, "toLowerCase", toStr, 0);
    attachMethod(sp, "toString", toStr, 0);
    attachMethod(sp, "toUpperCase", toStr, 0);
    // all Arrays returned by calls to split are merged in one
    var osplit = new Aobj({}), osplitaddr = ++count;
    var osplitav = makeObjAval(osplitaddr);
    heap[osplitaddr] = osplit;
    array_constructor([osplitav], true);
    osplit.updateNumProps(ASTR);
    attachMethod(sp, "split", function(args) {
      return new Ans(osplitav);
    }, 2);
    attachMethod(sp, "valueOf", toStr, 0);
    // create generic string object
    heap[++count] = new Aobj({proto : spav});
    generic_string_av = makeObjAval(count);

    // String
    function _String(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(spav); });
        return new Ans(args[0]);
      }
      return new Ans(ASTR);
    }
    var s = new Aobj({proto : o_pav, fun : funToNode("String", _String)});
    var saddr = ++count, sav = makeObjAval(saddr);
    heap[saddr] = s;
    go.addProp("String-", {aval : sav, enum : false});
    s.addProp("prototype-", {aval:spav, write:false, enum:false, config:false});
    sp.addProp("constructor-", {aval : sav, enum : false});
    attachMethod(s, "fromCharCode", toStr, 0);
  })();

  (function () {
    // Error.prototype
    var ep = new Aobj({proto:opav}), epaddr = ++count;
    var epav = makeObjAval(epaddr);
    heap[epaddr] = ep;
    attachMethod(ep, "toString", toStr, 0);

    // Error
    function _Error(args) {
      args[0].forEachObj(function (o) {
        o.updateProto(epav);
        o.addProp("message-", {aval : ASTR});
      });
      return new Ans(args[0]);
    }
    var e = new Aobj({proto : o_pav, fun : funToNode("Error", _Error)});
    var eaddr = ++count, eav = makeObjAval(eaddr);
    heap[eaddr] = e;
    go.addProp("Error-", {aval : eav, enum : false});
    e.addProp("prototype-", {aval:epav, write:false, enum:false, config:false});
    ep.addProp("constructor-", {aval : eav, enum : false});
    ep.addProp("name-", {aval : ASTR, enum : false});

    // SyntaxError.prototype
    var sep = new Aobj({proto:epav}), sepaddr = ++count;
    var sepav = makeObjAval(sepaddr);
    heap[sepaddr] = sep;

    // SyntaxError
    function _SyntaxError(args) {
      args[0].forEachObj(function (o) { 
        o.updateProto(sepav); 
        o.addProp("message-", {aval : ASTR});
      });
      return new Ans(args[0]);
    }
    var se = new Aobj({proto : o_pav,
                       fun : funToNode("SyntaxError", _SyntaxError)});
    var seaddr = ++count, seav = makeObjAval(seaddr);
    heap[seaddr] = se;
    go.addProp("SyntaxError-", {aval : seav, enum : false});
    se.addProp("prototype-",{aval:sepav, write:false, enum:false,config:false});
    sep.addProp("constructor-", {aval : seav, enum : false});
    sep.addProp("name-", {aval : ASTR});
  })();

  (function () {
    // RegExp.prototype
    var rp = new Aobj({proto:opav}), rpaddr = ++count;
    var rpav = makeObjAval(rpaddr);
    heap[rpaddr] = rp;
    // all Arrays returned by calls to exec are merged in one
    var oexec = new Aobj({}), oexecaddr = ++count;
    var oexecav = avjoin(ANULL, makeObjAval(oexecaddr));
    heap[oexecaddr] = oexec;
    array_constructor([oexecav], true);
    oexec.updateNumProps(ASTR);
    oexec.addProp("index-", {aval : ANUM});
    oexec.addProp("input-", {aval : ASTR});
    attachMethod(rp, "exec", function(args) { return new Ans(oexecav); }, 1);
    attachMethod(rp, "test", toBool, 1);

    // RegExp
    function _RegExp(args) {
      args[0].forEachObj(function (o) {
        o.updateProto(rpav);
        o.addProp("global-",{aval:ABOOL, write:false, enum:false,config:false});
        o.addProp("ignoreCase-", 
                  {aval:ABOOL, write:false, enum:false, config:false});
        o.addProp("lastIndex-", {aval : ANUM, enum : false, config : false});
        o.addProp("multiline-", 
                  {aval:ABOOL, write:false, enum:false, config:false});
        o.addProp("source-",{aval:ASTR, write:false, enum:false, config:false});
      });
      return new Ans(args[0]);
    }
    regexp_constructor = _RegExp;
    var r = new Aobj({proto : o_pav, fun : funToNode("RegExp", _RegExp)});
    var raddr = ++count, rav = makeObjAval(raddr);
    heap[raddr] = r;
    go.addProp("RegExp-", {aval : rav, enum : false});
    r.addProp("prototype-", {aval:rpav, write:false, enum:false, config:false});
    rp.addProp("constructor-", {aval : rav, enum : false});
  })();

  (function () {
    // Date.prototype
    var dp = new Aobj({proto:opav}), dpaddr = ++count;
    var dpav = makeObjAval(dpaddr);
    heap[dpaddr] = dp;
    attachMethod(dp, "getDate", toNum, 0);
    attachMethod(dp, "getDay", toNum, 0);
    attachMethod(dp, "getFullYear", toNum, 0);
    attachMethod(dp, "getHours", toNum, 0);
    attachMethod(dp, "getMilliseconds", toNum, 0);
    attachMethod(dp, "getMinutes", toNum, 0);
    attachMethod(dp, "getMonth", toNum, 0);
    attachMethod(dp, "getSeconds", toNum, 0);
    attachMethod(dp, "getTime", toNum, 0);
    attachMethod(dp, "getTimezoneOffset", toNum, 0);
    attachMethod(dp, "getYear", toNum, 0);
    attachMethod(dp, "setTime", toNum, 1);
    attachMethod(dp, "toString", toStr, 0);
    attachMethod(dp, "valueOf", toNum, 0);

    // Date
    function _Date(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(dpav); });
        return new Ans(args[0]);
      }
      return new Ans(ASTR);
    }
    var d = new Aobj({proto : o_pav, fun : funToNode("Date", _Date)});
    var daddr = ++count, dav = makeObjAval(daddr);
    heap[daddr] = d;
    go.addProp("Date-", {aval : dav, enum : false});
    d.addProp("prototype-", {aval:dpav, write:false, enum:false, config:false});
    dp.addProp("constructor-", {aval : dav, enum : false});
  })();

  (function () {
    // Math
    var m = new Aobj({proto : opav});
    var maddr = ++count, mav = makeObjAval(maddr);
    heap[maddr] = m;
    go.addProp("Math-", {aval : mav, enum : false});
    m.addProp("constructor-", {aval : oav, enum : false});
    m.addProp("E-", {aval : ANUM, write : false, enum : false, config : false});
    m.addProp("LN10-",{aval : ANUM, write : false, enum : false, config:false});
    m.addProp("LN2-", {aval : ANUM, write : false, enum : false, config:false});
    m.addProp("LOG10E-", {aval : ANUM, write:false, enum:false, config:false});
    m.addProp("LOG2E-", {aval : ANUM, write:false, enum:false, config:false});
    m.addProp("PI-", {aval : ANUM, write : false, enum : false, config :false});
    m.addProp("SQRT1_2-", {aval : ANUM, write:false, enum:false, config:false});
    m.addProp("SQRT2-",{aval:ANUM, write:false, enum:false, config:false});
    attachMethod(m, "abs", toNum, 1);
    attachMethod(m, "acos", toNum, 1);
    attachMethod(m, "asin", toNum, 1);
    attachMethod(m, "atan", toNum, 1);
    attachMethod(m, "atan2", toNum, 1);
    attachMethod(m, "ceil", toNum, 1);
    attachMethod(m, "cos", toNum, 1);
    attachMethod(m, "exp", toNum, 1);
    attachMethod(m, "floor", toNum, 1);
    attachMethod(m, "log", toNum, 1);
    attachMethod(m, "max", toNum, 0);
    attachMethod(m, "min", toNum, 0);
    attachMethod(m, "pow", toNum, 2);
    attachMethod(m, "random", toNum, 0);
    attachMethod(m, "round", toNum, 1);
    attachMethod(m, "sin", toNum, 1);
    attachMethod(m, "sqrt", toNum, 1);
    attachMethod(m, "tan", toNum, 1);
  })();

  (function () {
    // Boolean.prototype
    var bp = new Aobj({proto:opav}), bpaddr = ++count;
    var bpav = makeObjAval(bpaddr);
    heap[bpaddr] = bp;
    attachMethod(bp, "toString", toStr, 0);
    attachMethod(bp, "valueOf", toBool, 0);
    // create generic boolean object
    heap[++count] = new Aobj({proto : bpav});
    generic_boolean_av = makeObjAval(count);

    // Boolean
    function _Boolean(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(bpav); });
        return new Ans(args[0]);
      }
      return new Ans(ABOOL);
    }
    var b = new Aobj({proto : o_pav, fun : funToNode("Boolean", _Boolean)});
    var baddr = ++count, bav = makeObjAval(baddr);
    heap[baddr] = b;
    go.addProp("Boolean-", {aval : bav, enum : false});
    b.addProp("prototype-", {aval:bpav, write:false, enum:false, config:false});
    bp.addProp("constructor-", {aval : bav, enum : false});
  })();
}


////////////////////////////////////////////////////////////////////////////////
//////////////////////////   EVALUATION PREAMBLE   /////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// frame, identifier node, Aval -> undefined
function frameSet(fr, param, val) {
  fr[param.addr] = [val, timestamp]; // record when param was bound to val
}

// frame, identifier node -> Aval
function frameGet(fr, param) {
  var pa = param.addr, binding = fr[pa];
  if (binding[1] < modified[pa]) {
    // if binding changed in heap, change it in frame to be sound
    binding[0] = avjoin(binding[0], heap[pa]);
    binding[1] = timestamp;
  }
  return binding[0];
}

// fun. node, array of Aval, timestamp  -> [Aval, Aval] or false
function searchSummary(n, args, ts) {
  var n_summaries = summaries[n.addr], insouts, summary;
  if (n_summaries.ts < ts) return false;
  insouts = n_summaries.insouts;
  for (var i = 0, len = insouts.length; i < len; i++) {
    summary = insouts[i];
    if (arrayeq(aveq, args, summary[0])) return summary.slice(-2);
  }
  return false;
}

// function node -> boolean
// check if any summary exists for this function node
function existsSummary(n) {
  return summaries[n.addr].ts !== INVALID_TIMESTAMP;
}

// fun. node, array of Aval, Aval, Aval or undefined, timestamp  -> undefined
function addSummary(n, args, retval, errval, ts) {
  var addr = n.addr, summary = summaries[addr];
  if (summary.ts === ts)
    summary.insouts.push([args, retval, errval]);
  else if (summary.ts < ts) { // discard summaries for old timestamps.
    summary.ts = ts;
    summary.insouts = [[args, retval, errval]];
  }
  // join new summary w/ earlier ones.
  var insjoin = summary.type[0];
  for (var i = 0, len = insjoin.length; i < len; i++)
    insjoin[i] = avjoin(insjoin[i], args[i] || AUNDEF/*arg mismatch*/);
  summary.type[1] = avjoin(summary.type[1], retval);
  summary.type[2] = maybeavjoin(summary.type[2], errval);
}

// function node, optional array -> string
// The second arg is used by recursive calls only, to avoid cycles.
function funToType(n, seenObjs) {
  if (n.builtin)
    return "function"; // FIXME: tag built-in nodes w/ their types
  if (seenObjs) {
    if (seenObjs.member(function(o) { return o === n; }))
      return "any";
    else
      seenObjs.push(n);
  }
  else
    seenObjs = [n];
  
  var addr = n.addr, summary = summaries[addr];
  if (summary.ts === INVALID_TIMESTAMP) // the function was never called
    return "function";
  var insjoin = summary.type[0], instypes = [], outtype, slen = seenObjs.length;
  for (var i = 1, len = insjoin.length; i < len; i++) {
    instypes[i - 1] = insjoin[i].toType(seenObjs);
    // each argument must see the same seenObjs, the initial one.
    seenObjs.splice(slen, seenObjs.length);
  }

  if (n.withNew && !n.hasReturn) {
    outtype = n.fname.name;
    // If a fun is called both w/ and w/out new, assume it's a constructor.
    // If a constructor is called w/out new, THIS is bound to the global obj.
    // In this case, the result type must contain void.
    var thisObjType = insjoin[0].toType(seenObjs);
    if (/Global Object/.test(thisObjType))
      outtype = "<void | " + outtype + ">";
  }
  else
    outtype = summary.type[1].toType(seenObjs);
  
  if (outtype === "undefined") outtype = "void";
  return (outtype + " function(" + instypes.join(", ") +")");
}

function showSummaries() {
  for (var addr in summaries) {
    var f = flags[addr];
    //print(f.fname.name + ": " + funToType(f));
  }
}

// array of Aval -> number
// Hash an array of args using arg 1 only. May change if it doesn't hash well.
function hash(avs) {
  if (avs[0])
    return avs[0].hash();
  else
    return 0;
}

// function node, array of Aval -> [args, timestamp, depth, boolean] or false
function searchPending(n, args) {
  var bucket = pending[n.addr][hash(args)];
  if (!bucket) return false;
  // start from the end to find the elm that was pushed last
  for (var i = bucket.length - 1; i >=0; i--)
    if (arrayeq(aveq, args, bucket[i][0]))
      return bucket[i];
  return false;
}

var maxBucketSize;

// function node, [args, timestamp, depth, boolean] -> undefined
function addPending(n, elm) {
  var a = n.addr, h = hash(elm[0]), bucket = pending[a][h];
  if (!bucket)
    pending[a][h] = [elm];
  else {
    // maxBucketSize = Math.max(maxBucketSize, bucket.length);
    
    bucket.push(elm);
  }
}

// elm is last in its bucket in pending
function rmPending(n, elm) {
  pending[n.addr][hash(elm[0])].pop();
}

// evalExp & friends use Ans to return tuples
function Ans(v, fr, err) {
  this.v = v; // evalExp puts abstract values here, evalStm puts statements
  this.fr = fr; // frame
  err && (this.err = err); // Aval for exceptions thrown
}


// Initialize the heap for each fun decl, var decl and heap var.
// Because of this function, we never get undefined by reading from heap.
// Must be run after initGlobals and after initCoreObjs.
// Most Aobj`s that aren't core are created here.

// jump table for initDeclsExp
var initDeclsExp = [];

(function() {

  function _multi(n) {
    // fixme: when array elms have the same type, they can be prematurely
    // merged to help the speed of the algo e.g. in 3d-cube
    if (n.type === ARRAY_INIT) {
      heap[n.addr] = new Aobj({});
      array_constructor([makeObjAval(n.addr)], true);
    }
    n.forEach(function(e) { initDeclsExp[opArity[e.type]](e); });
  }

  function _recurInit(n) { 
    n.forEach(function(e) { initDeclsExp[opArity[e.type]](e); });
  }

  function _call(n) {
    if (n.type === NEW_WITH_ARGS) heap[n.addr] = new Aobj({});
    initDeclsExp[opArity[n[0].type]](n[0]);
    n[1].forEach(function(e) { initDeclsExp[opArity[e.type]](e); });
  }

  function _nullary(n) {
    if (n.type === REGEXP) {
      heap[n.addr] = new Aobj({});
      regexp_constructor([makeObjAval(n.addr)]);
    }
  }

  function _fun(n) {
    var objaddr = n.addr, fn = n.fname, 
    obj = new Aobj({fun:n, proto:function_prototype_av});
    // heap[objaddr] will point to this object throughout the analysis.
    heap[objaddr] = obj;
    obj.addProp("prototype-", {aval:BOTTOM, enum:false});
    if (fn.kind === HEAP)
      heap[fn.addr] = makeObjAval(objaddr);
    n.params.forEach(function(p) {if (p.kind === HEAP) heap[p.addr] = BOTTOM;});
    flags[objaddr] = n;
    // initialize summaries and pending
    summaries[objaddr] = {
      ts: INVALID_TIMESTAMP,
      insouts: [],
      type: [buildArray(n.params.length + 1, BOTTOM), BOTTOM]//arg 0 is for THIS
    };
    pending[objaddr] = {};
    initDeclsInHeap[n.body.type](n.body);
  }

  function _obj_init(n) {
    heap[n.addr] = new Aobj({proto:object_prototype_av});
    n.forEach(function(prop) {
      if (prop.type !== GETTER && prop.type !== SETTER) {
        initDeclsExp[opArity[prop[0].type]](prop[0]);
        initDeclsExp[opArity[prop[1].type]](prop[1]);
      }
    });
  }

  initDeclsExp[UNARY] = _recurInit;
  initDeclsExp[BINARY] = _recurInit;
  initDeclsExp[TERNARY] = _recurInit;
  initDeclsExp[MULTI] = _multi;
  initDeclsExp[MULTI_CALL] = _call;
  initDeclsExp[NULLARY] = _nullary;
  initDeclsExp[MULTI_OI] = _obj_init;
  initDeclsExp[FUN] = _fun;
})();

// jump table for initDeclsInHeap
var initDeclsInHeap = [];

(function() {

  function _script(n) {
    n.funDecls.forEach(initDeclsExp[FUN]);
    n.varDecls.forEach(function(vd) { 
      if (flags[vd.addr]) heap[vd.addr] = BOTTOM;
    });
    n.forEach(function(s) { initDeclsInHeap[s.type](s); });
  }

  function _block(n) { 
    n.forEach(function(s) { initDeclsInHeap[s.type](s); });
  }

  function _fun(n) { initDeclsExp[FUN](n); }

  function _if(n) {
    initDeclsExp[opArity[n.condition.type]](n.condition);
    initDeclsInHeap[n.thenPart.type](n.thenPart);
    n.elsePart && initDeclsInHeap[n.elsePart.type](n.elsePart);
  }
    
  function _switch(n) {
    initDeclsExp[opArity[n.discriminant.type]](n.discriminant);
    n.cases.forEach(function(branch) { 
      initDeclsInHeap[branch.statements.type](branch.statements); 
    });
  }

  function _for(n) {
    n.setup && initDeclsExp[opArity[n.setup.type]](n.setup);
    n.condition && initDeclsExp[opArity[n.condition.type]](n.condition);
    n.update && initDeclsExp[opArity[n.update.type]](n.update);
    initDeclsInHeap[n.body.type](n.body);
  }

  function _for_in(n) {
    initDeclsExp[opArity[n.iterator.type]](n.iterator);
    initDeclsExp[opArity[n.object.type]](n.object);
    initDeclsInHeap[n.body.type](n.body);
  }

  function _while_do(n) {
    initDeclsExp[opArity[n.condition.type]](n.condition);
    initDeclsInHeap[n.body.type](n.body);
  }

  function _try(n) {
    initDeclsInHeap[n.tryBlock.type](n.tryBlock);
    n.catchClauses.forEach(function(clause) {
      clause.guard && initDeclsExp[opArity[clause.guard.type]](clause.guard);
      initDeclsInHeap[clause.block.type](clause.block);
    });
    n.finallyBlock && initDeclsInHeap[n.finallyBlock.type](n.finallyBlock);
  }

  function _ret(n) { 
    initDeclsExp[opArity[n.value.type]](n.value); 
  }

  function _throw(n) { initDeclsExp[opArity[n.exception.type]](n.exception); }

  function _semi(n) { initDeclsExp[opArity[n.expression.type]](n.expression); }

  initDeclsInHeap[FUNCTION] = _fun;
  initDeclsInHeap[SCRIPT] = _script;
  initDeclsInHeap[BLOCK] = _block;
  initDeclsInHeap[SEMICOLON] = _semi;
  initDeclsInHeap[IF] = _if;
  initDeclsInHeap[SWITCH] = _switch;
  initDeclsInHeap[FOR] = _for;
  initDeclsInHeap[FOR_IN] = _for_in;
  initDeclsInHeap[WHILE] = _while_do;
  initDeclsInHeap[DO] = _while_do;
  initDeclsInHeap[TRY] = _try;
  initDeclsInHeap[THROW] = _throw;
  initDeclsInHeap[RETURN] = _ret;
})();

// nothing -> Aval
// Used to analyze functions that aren't called
function makeGenericObj() {
  var gobj = new Aobj({proto : object_prototype_av}), gobjaddr = ++count;
  heap[gobjaddr] = gobj;
  return makeObjAval(gobjaddr);
}


////////////////////////////////////////////////////////////////////////////////
//////////////////////////   EVALUATION FUNCTIONS   ////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// jump table for evaluating lvalues
var evalLval = [];

(function() {
  // node, Ans, optional Aval -> Ans
  // use n to get an lvalue, do the assignment and return the rvalue

  function _stackref(n, ans, oldlval) {
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        ans.v = aplus(ans.v, oldlval);
      else
        ans.v = ANUM;
    }
    var newav = avjoin(frameGet(ans.fr, n), ans.v);
    frameSet(ans.fr, n, newav);
    // if n is a heap var, update heap so its heap refs get the correct Aval.
    if (flags[n.addr]) updateHeapAv(n.addr, newav);
    return ans;
  }

  function _heapref(n, ans, oldlval) {
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        ans.v = aplus(ans.v, oldlval);
      else
        ans.v = ANUM;
    }
    updateHeapAv(n.addr, ans.v);
    return ans;
  }

  function _index(n, ans, oldlval) {
    var rval = ans.v, fr = ans.fr, errval;
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        rval = aplus(rval, oldlval);
      else
        rval = ANUM;
    }
    var prop = n[1], pt = prop.type;
    var ansobj = evalExp[n[0].type](n[0], fr), avobj = ansobj.v;
    fr = ansobj.fr;
    errval = ansobj.err;
    // Unsound: ignore everything the index can eval to except numbers & strings
    if (pt === STRING)
      avobj.updateProp(prop.value, rval);
    else {
      var ansprop = evalExp[pt](prop, fr), avprop = ansprop.v;
      fr = ansprop.fr;
      errval = maybeavjoin(errval, ansprop.err);
      if (avprop.hasNum()) 
        avobj.forEachObj(function(o) { o.updateNumProps(rval); });
      if (avprop.hasStr()) {
        var slit = avprop.getStrLit();
        if (slit)
          avobj.updateProp(slit, rval);
        else
          avobj.forEachObj(function(o) { o.updateStrProps(rval); });
      }
    }
    return new Ans(rval, fr, maybeavjoin(errval, ans.err));
  }

  function _dot(n, ans, oldlval) {
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        ans.v = aplus(ans.v, oldlval);
      else
        ans.v = ANUM;
    }
    var ans2 = evalExp[n[0].type](n[0], ans.fr);
    ans2.v.updateProp(n[1].name, ans.v);
    ans.fr = ans2.fr;
    ans.err = maybeavjoin(ans.err, ans2.err);
    return ans;
  }

  function _arguments(n, ans, oldlval) {
    // FIXME: handle assignment to the arguments array
    return ans;
  }

  evalLval[IDENTIFIER] = function(n, ans, oldlval) {
    if (n.kind === STACK)
      return _stackref(n, ans, oldlval);
    else
      return _heapref(n, ans, oldlval);
  };
  evalLval[INDEX] = _index;
  evalLval[DOT] = _dot;
  evalLval[DOT_PROTO] = _dot;
  evalLval[ARGUMENTS] = _arguments;
})();

// jump table for evaluating expressions
var evalExp = [];

(function() {
  // node, frame -> Ans

  function _stackref(n, fr) { return new Ans(frameGet(fr, n), fr); }

  function _heapref(n, fr) { return new Ans(heap[n.addr], fr); }

  function _num(n, fr) { return new Ans(ANUM, fr); }

  function _str(n, fr) { return new Ans(makeStrLitAval(n.value), fr); }

  function _bool(n, fr) { return new Ans(ABOOL, fr); }

  function _null(n, fr) { return new Ans(ANULL, fr); }

  function _regexp(n, fr) { return new Ans(makeObjAval(n.addr), fr); }

  function _this(n, fr) { return new Ans(fr.thisav, fr); }

  function _unary2num(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr);
    ans.v = ANUM;
    return ans;
  }

  function _not(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr);
    ans.v = ABOOL;
    return ans;
  }

  function _typeof(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr);
    ans.v = ASTR;
    return ans;
  }

  function _void(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr);
    ans.v = AUNDEF;
    return ans;
  }

  function _delete(n, fr) { // unsound: I'm not deleting anything
    var ans = evalExp[n[0].type](n[0], fr);
    ans.v = avjoin(ABOOL, AUNDEF);
    return ans;
  }

  function _binary2bool(n, fr) {
    var ans1 = evalExp[n[0].type](n[0], fr);
    var ans2 = evalExp[n[1].type](n[1], ans1.fr);
    ans2.v = ABOOL;
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;
  }

  function _andor(pred1, pred2) {
    return function(n, fr) {
      var ans1 = evalExp[n[0].type](n[0], fr), av = ans1.v;
      if (pred1.call(av)) return ans1;
      var ans2 = evalExp[n[1].type](n[1], ans1.fr);
      ans2.err = maybeavjoin(ans1.err, ans2.err);
      if (!pred2.call(av)) ans2.v = avjoin(av, ans2.v);
      return ans2;
    }
  }

  function _plus(n, fr) {
    var ans1 = evalExp[n[0].type](n[0], fr);
    var ans2 = evalExp[n[1].type](n[1], ans1.fr);
    ans2.v = aplus(ans1.v, ans2.v);
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;
  }

  function _binary2num(n, fr) {
    var ans1 = evalExp[n[0].type](n[0], fr);
    var ans2 = evalExp[n[1].type](n[1], ans1.fr);
    ans2.v = ANUM;
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;
  }

  function _plus_assign(n, fr) {
    // recomputing n[0] for += is better than checking every lhs in evalLval
    var ans = evalExp[n[0].type](n[0], fr);
    return evalLval[n[0].type](n[0], evalExp[n[1].type](n[1], fr), ans.v);
  }

  function _assign(n, fr) {
    return evalLval[n[0].type](n[0], evalExp[n[1].type](n[1], fr));
  }

  function _hook(n, fr) {
    var nt = n.type, ans = evalExp[n[0].type](n[0], fr);
    var ans1 = evalExp[n[1].type](n[1], ans.fr);
    var ans2 = evalExp[n[2].type](n[2], ans1.fr);
    ans2.err = maybeavjoin(ans.err, maybeavjoin(ans1.err, ans2.err));
    ans2.v = avjoin(ans1.v, ans2.v);
    return ans2;
  }

  function _function(n, fr) {
    return new Ans(makeObjAval(n.addr), fr);
  }

  function _comma(n, fr) {
    var nt = n.type, ans, av, errval;
    n.forEach(function(exp) {
      ans = evalExp[exp.type](exp, fr);
      av = ans.v; // keep last one
      fr = ans.fr;
      errval = maybeavjoin(errval, ans.err);
    });
    ans.v = av;
    ans.err = errval;
    return ans;
  }

  function _obj_init(n, fr) {
    var nt = n.type, ans, errval, objaddr = n.addr, newobj = heap[objaddr];
    n.forEach(function(pinit) {
      if (pinit.type === GETTER || pinit.type === SETTER)
        return;

      ans = evalExp[pinit[1].type](pinit[1], fr);
      fr = ans.fr;
      newobj.updateProp(pinit[0].name, ans.v);
      errval = maybeavjoin(errval, ans.err);
    });
    return new Ans(makeObjAval(objaddr), fr, errval);
  }

  function _array_init(n, fr) {
    var nt =n.type, ans, errval, arrayaddr = n.addr, newarray = heap[arrayaddr];
    n.forEach(function(elm, i) {
      ans = evalExp[elm.type](elm, fr);
      fr = ans.fr;
      newarray.updateProp(i + "-", ans.v);
      errval = maybeavjoin(errval, ans.err);
    });
    return new Ans(makeObjAval(arrayaddr), fr, errval);
  }

  function _dot_proto(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr), ans2, av = BOTTOM, av2,
    errval = ans.err;
    // FIXME: record error if ans.v contains base values
    ans.v.forEachObj(function(o) {
      var clos = o.getFun(), proto;
      if (!clos) { // if o isn't a function, this is just a property access
        av2 = o.getProp("prototype-");
        av = avjoin(av, av2 || AUNDEF);
      }
      else {
        proto = o.getProp("prototype-");
        if (!aveq(BOTTOM, proto))
          av = avjoin(av, proto);
        else {// create default prototype and return it
          proto = makeDefaultProto(clos);
          o.updateProp("prototype-", proto);
          av = avjoin(av, proto);
        }
      }
    });
    ans2 = new Ans(av, ans.fr, errval);
    ans2.thisav = ans.v; // used by method calls
    return ans2;
  }

  function _index(n, fr) {

    var ansobj = evalExp[n[0].type](n[0], fr), avobj = ansobj.v.baseToObj(),
    prop = n[1], pt = prop.type, errval = ansobj.err, av , ans;
    fr = ansobj.fr;
    // If [] notation is used with a constant, try to be precise.
    // Unsound: ignore everything the index can eval to except numbers & strings
    if (pt === STRING)
      av = avobj.getProp(prop.value);
    else {
      var ansprop = evalExp[pt](prop, fr), avprop = ansprop.v;
      fr = ansprop.fr;
      errval = maybeavjoin(errval, ansprop.err);
      av = BOTTOM;
      if (avprop.hasNum())
        avobj.forEachObj(function(o) { av = avjoin(av, o.getNumProps()); });
      if (avprop.hasStr()) {
        var slit = avprop.getStrLit();
        if (slit)
          av = avjoin(av, avobj.getProp(slit));
        else
          avobj.forEachObj(function(o) { av = avjoin(av, o.getStrProps()); });
      }
    }
    ans = new Ans(av, fr, errval);
    ans.thisav = avobj;
    return ans;
  }

  function _dot(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr), avobj = ans.v.baseToObj();
    ans.thisav = avobj; // used by method calls
    ans.v = avobj.getProp(n[1].name);
    return ans;
  }

  function _call(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr), ans1, errval, rands = [];
    rands.push(ans.thisav ? ans.thisav : global_object_av);
    fr = ans.fr;
    errval = ans.err;
    // evaluate arguments
    n[1].forEach(function(rand) {
      ans1 = evalExp[rand.type](rand, fr);
      rands.push(ans1.v);
      fr = ans1.fr;
      errval = maybeavjoin(errval, ans1.err);
    });
    // call each function that can flow to the operator position
    ans = ans.v.callFun(rands, n);
    ans.fr = fr;
    ans.err = maybeavjoin(errval, ans.err);
    return ans;
  }

  function _new_with_args(n, fr) {
    var rands = [], retval = BOTTOM;
    var ans = evalExp[n[0].type](n[0], fr), ans1, errval;
    var objaddr = n.addr, thisobj = heap[objaddr];
    rands.push(makeObjAval(objaddr));
    fr = ans.fr;
    errval = ans.err;
    // evaluate arguments
    n[1].forEach(function(rand) {
      ans1 = evalExp[rand.type](rand, fr);
      rands.push(ans1.v);
      fr = ans1.fr;
      errval = maybeavjoin(errval, ans1.err);
    });
    // FIXME: record error if rator contains base vals and non-functions
    ans.v.baseToObj().forEachObj(function(o) {
      var clos = o.getFun(), proto;
      if (!clos) return;
      proto = o.getProp("prototype-");
      if (aveq(BOTTOM, proto)) {
        // create default prototype & use it
        proto = makeDefaultProto(clos);
        o.updateProp("prototype-", proto);
      }
      thisobj.updateProto(proto);
      // if a fun is called both w/ and w/out new, assume it's a constructor
      clos.withNew = true;
      ans = evalFun(clos, rands, true, n);
      if (clos.hasReturn) // constructor uses return
        retval = avjoin(retval, ans.v);
      else // constructor doesn't use return
        retval = avjoin(retval, rands[0]);
      errval = maybeavjoin(errval, ans.err);
    });
    return new Ans(retval, fr, errval);
  }

  function _arguments(n, fr) {
    var index = n[0], ps = n.arguments, restargs = fr[RESTARGS] || BOTTOM;
    var ans, av, errval;
    if (index.type === NUMBER) {
      var iv = index.value;
      if (iv < 0)
        av = AUNDEF;
      else if (iv < ps.length)
        av = frameGet(fr, ps[iv]);
      else
        av = restargs; // unsound: not checking if iv > #args
    }
    else {
      ans = evalExp[index.type](index, fr);
      fr = ans.fr;
      errval = ans.err;
      av = BOTTOM;
      // when we don't know the index, we return the join of all args
      ps.forEach(function(p) { av = avjoin(av, frameGet(fr, p)); });
      av = avjoin(av, restargs);
    }
    return new Ans(av, fr, errval);
  }

  evalExp[IDENTIFIER] = function(n, fr) {
    if (n.kind === STACK)
      return _stackref(n, fr);
    else
      return _heapref(n, fr);
  };
  evalExp[NUMBER]        = _num;
  evalExp[STRING]        = _str;
  evalExp[TRUE]          = _bool;
  evalExp[FALSE]         = _bool;
  evalExp[NULL]          = _null;
  evalExp[REGEXP]        = _regexp;
  evalExp[THIS]          = _this;
  evalExp[UNARY_PLUS]    = _unary2num;
  evalExp[UNARY_MINUS]   = _unary2num;
  evalExp[INCREMENT]     = _unary2num;
  evalExp[DECREMENT]     = _unary2num;
  evalExp[BITWISE_NOT]   = _unary2num;
  evalExp[NOT]           = _not;
  evalExp[TYPEOF]        = _typeof;
  evalExp[VOID]          = _void;
  evalExp[DELETE]        = _delete;
  evalExp[EQ]            = _binary2bool;
  evalExp[NE]            = _binary2bool;
  evalExp[STRICT_EQ]     = _binary2bool;
  evalExp[STRICT_NE]     = _binary2bool;
  evalExp[LT]            = _binary2bool;
  evalExp[LE]            = _binary2bool;
  evalExp[GE]            = _binary2bool;
  evalExp[GT]            = _binary2bool;
  evalExp[INSTANCEOF]    = _binary2bool;
  evalExp[IN]            = _binary2bool;
  evalExp[AND]           = _andor(Aval.prototype.isFalsy, 
                                  Aval.prototype.isTruthy);
  evalExp[OR]            = _andor(Aval.prototype.isTruthy, 
                                  Aval.prototype.isFalsy);
  evalExp[PLUS]          = _plus;
  evalExp[MINUS]         = _binary2num;
  evalExp[MUL]           = _binary2num;
  evalExp[DIV]           = _binary2num;
  evalExp[MOD]           = _binary2num;
  evalExp[BITWISE_OR]    = _binary2num;
  evalExp[BITWISE_XOR]   = _binary2num;
  evalExp[BITWISE_AND]   = _binary2num;
  evalExp[LSH]           = _binary2num;
  evalExp[RSH]           = _binary2num;
  evalExp[URSH]          = _binary2num;
  evalExp[PLUS_ASSIGN]   = _plus_assign;
  evalExp[ASSIGN]        = _assign;
  evalExp[HOOK]          = _hook;
  evalExp[FUNCTION]      = _function;
  evalExp[COMMA]         = _comma;
  evalExp[OBJECT_INIT]   = _obj_init;
  evalExp[ARRAY_INIT]    = _array_init;
  evalExp[DOT_PROTO]     = _dot_proto;
  evalExp[DOT]           = _dot;
  evalExp[INDEX]         = _index;
  evalExp[CALL]          = _call;
  evalExp[NEW_WITH_ARGS] = _new_with_args;
  evalExp[ARGUMENTS]     = _arguments;
})();

// jump table for evaluating statements
var evalStm = [];

(function() {
  // node, frame -> Ans
  // evaluate the statement and find which statement should be executed next.

  function _semicolon(n, fr) {
    var nexp = n.expression, ans = evalExp[nexp.type](nexp, fr);
    ans.v = n.kreg;
    return ans;
  }

  function _next(n, fr) { return new Ans(n.kreg, fr); }

  function _for_in(n, fr) {
    // For most kinds of iterators at FOR/IN we have to be conservative 
    // (e.g. DOTs or INDEXes). Without flow sensitivity, we even have to be
    // conservative for stack refs that have been initialized, we can't forget
    // their current value. We can only be precise when the iterator is a stack
    // reference and the variable is BOTTOM in the frame.
    var ans = evalExp[n.object.type](n.object, fr), errval, av;
    var it = n.iterator, b = n.body, bt;
    if (it.type === IDENTIFIER && 
        it.kind === STACK && 
        aveq(BOTTOM, frameGet(fr, it))) {

      av = ans.v;
      errval = ans.err;
      bt = b.type;
      av.forEachObj(function(o) {
        o.forEachEnumProp(function(p) {
          // wipe the value of it from the previous iteration
          frameSet(fr, it, makeStrLitAval(p));
          if (flags[it.addr]) updateHeapAv(it.addr, makeStrLitAval(p));
          ans = evalStm[bt](b, fr);
          errval = maybeavjoin(errval, ans.err);
        });
      });
      ans.v = b.kreg;
      ans.err = errval;
    }
    else {
      av = BOTTOM;
      ans.v.forEachObj(function(o) {
        o.forEachEnumProp(function(p) {
          if (propIsNumeric(p)) 
            av = avjoin(av, ANUM);
          else
            av = avjoin(av, ASTR);
        });
      });
      ans.v = av;
      ans = evalLval[n.iterator.type](n.iterator, ans);
      ans.v = b;
    }
    return ans;
  }

  function _catch(n, fr) { return new Ans(n.block, fr); }

  function _throw(n, fr) {
    var ans = evalExp[n.exception.type](n.exception, fr);
    ans.err = maybeavjoin(ans.err, ans.v);
    ans.v = n.kreg;
    return ans;
  }

  evalStm[CATCH]     = _catch;
  evalStm[FOR_IN]    = _for_in;
  evalStm[SEMICOLON] = _semicolon;
  evalStm[THROW]     = _throw;
  evalStm[BLOCK]     = _next;
  evalStm[CASE]      = _next;
  evalStm[DEFAULT]   = _next;
  evalStm[DO]        = _next;
  evalStm[FINALLY]   = _next;
  evalStm[FOR]       = _next;
  evalStm[IF]        = _next;
  evalStm[SWITCH]    = _next;
  evalStm[TRY]       = _next;
  evalStm[WHILE]     = _next;
})();

var big_ts;
var rethrows;
var callsEvalFun;
var noSum;

// function node, array of Aval, boolean, optional call node -> Ans w/out fr
// Arg 4 is the node that caused the function call (if there is one).
function evalFun(fn, args, withNew, cn) {
  var ans, n, params, fr, w, retval, errval, script = fn.body, pelm1;

  // stm node (exception continuation), av (exception value) -> undefined
  function stmThrows(n, errav) {
    if (n) {
      if (n.type === CATCH) {
        var exvar = n.exvar;
        if (fr[exvar.addr]) // revealing the representation of frame here.
          frameSet(fr, exvar, avjoin(errav, frameGet(fr, exvar)));
        else
          frameSet(fr, exvar, errav);
      }
      w.push(n);
    }
    else
      errval = maybeavjoin(errval, errav);
  }

  // if (timestamp > big_ts) {
  //   print("big ts: " + timestamp);
  //   big_ts += 1000;
  //   if (big_ts > 100000) throw new Error("foobar");
  // }

  // treat built-in functions specially
  if (fn.builtin) return fn.body(args, withNew, cn);

  ++callsEvalFun; // don't count the built-ins

  var tsAtStart;
  var result = searchSummary(fn, args, timestamp);
  if (result) return new Ans(result[0], undefined, result[1]);

  ++depth;

  while(true) {
    try {
      tsAtStart = timestamp;
      // Using pending & exceptions is an attempt to prevent the runtime stack 
      // from growing too much.
      var pelm2 = searchPending(fn, args), p2ts = pelm2 && pelm2[1];
      if (!p2ts) {
        pelm1 = [args, timestamp, depth, false];
        addPending(fn, pelm1);
        ++noSum;
      }
      else if (p2ts === timestamp) {
        // When a call eventually leads to itself, we can't stop processing and
        // return BOTTOM because the context won't get the correct type for the 
        // recursive function. We stop processing when we see a call twice.
        if (pelm2[3]) {
          --depth;
          return new Ans(BOTTOM);
        }
        else {
          pelm1 = [args, timestamp, depth, true];
          addPending(fn, pelm1);
          ++noSum;
        }
      }
      else /* if (p2ts < timestamp) */ {
        // rethrows++;
        
        // There are pending calls that are obsolete because their timestamp is
        // old. Discard frames to not grow the stack too much.
        var e = new Error();
        e.depth = pelm2[2];
        throw e;
      }

      w = [];
      fr = {};
      retval = BOTTOM;
      params = fn.params;
      frameSet(fr, fn.fname, makeObjAval(fn.addr));
      // args[0] is always the obj that THIS is bound to.
      // THIS never has a heap ref, so its entry in the frame is special.
      fr.thisav = args[0];
      // Bind formals to actuals
      for (var i = 0, len = params.length; i < len; i++) {
        var param = params[i], arg = args[i+1] || AUNDEF;//maybe #args < #params
        if (param.kind === HEAP) updateHeapAv(param.addr, arg);
        frameSet(fr, param, arg);
      }
      var argslen = args.length;
      if ((++i) < argslen) { // handling of extra arguments
        var restargs = BOTTOM;
        for (; i<argslen; i++) restargs = avjoin(restargs, args[i]);
        fr[RESTARGS] = restargs; // special entry in the frame.
      }
      // bind a non-init`d var to bottom, not undefined.
      script.varDecls.forEach(function(vd) { frameSet(fr, vd, BOTTOM); });
      // bind the fun names in the frame.
      script.funDecls.forEach(function(fd) {
        frameSet(fr, fd.fname, makeObjAval(fd.addr));
      });

      w.push(script.kreg);
      while (w.length !== 0) {
        n = w.pop();
        if (n === undefined) continue;
        if (n.type === RETURN) {
          ans = evalExp[n.value.type](n.value, fr);
          // fr is passed to exprs/stms & mutated, no need to join(fr, ans.fr)
          fr = ans.fr;
          retval = avjoin(retval, ans.v);
          w.push(n.kreg);
          if (ans.err) stmThrows(n.kexc, ans.err);
        }
        else {
          ans = evalStm[n.type](n, fr);
          fr = ans.fr;
          w.push(ans.v);
          if (ans.err) stmThrows(n.kexc, ans.err);
        }
      }
      rmPending(fn, pelm1);
      --depth;
      if (!fn.hasReturn) retval = AUNDEF;
      addSummary(fn, args, retval, errval, tsAtStart);
      return new Ans(retval, undefined, errval);
    }
    catch (e) {
      if (!pelm1) {
        --depth;
        throw e;
      }
      if (e.depth === depth) {
        // when reaching here, there's only one matching elm in pending and it
        // wasn't added during recursion, its boolean is false.
        rmPending(fn, pelm1);
      }
      else {
        //if (e.depth === pelm1[2]) throw new Error("FIXME: bug in algo");
        rmPending(fn, pelm1);
        --depth;
        throw e;
      }
    }
  }
}

// maybe merge with evalFun at some point
function evalToplevel(tl) {
  var w /* workset */, fr, n, ans;
  w = [];
  fr = {};
  initDeclsInHeap[SCRIPT](tl);

  fr.thisav = global_object_av;
  // bind a non-init`d var to bottom, different from assigning undefined to it.
  tl.varDecls.forEach(function(vd) { frameSet(fr, vd, BOTTOM); });
  // bind the fun names in the frame.
  tl.funDecls.forEach(function(fd) { 
    frameSet(fr, fd.fname, makeObjAval(fd.addr));
  });

  // evaluate the stms of the toplevel in order
  w.push(tl.kreg);
  while (w.length !== 0) {
    n = w.pop();
    if (n === undefined) continue; // end of toplevel reached
    if (n.type === RETURN)
      ; // record error, return in toplevel
    else {
      ans = evalStm[n.type](n, fr);
      fr = ans.fr;
      w.push(ans.v);
      // FIXME: handle toplevel uncaught exception
    }
  }

  //print("call uncalled functions");
  
  // each function w/out a summary is called with unknown arguments
  for (var addr in summaries) {
    var f = flags[addr];
    if (!existsSummary(f)) {
      var any_args = buildArray(f.params.length, BOTTOM);
      any_args.unshift(makeGenericObj());
      evalFun(f, any_args, false);
    }
  }

  //showSummaries();
}

// initGlobals and initCoreObjs are difficult to override. The next 2 vars help
// clients of the analysis add stuff to happen during initialization
var initOtherGlobals, initOtherObjs;

// consumes the ast returned by jsparse.parse
function cfa2(ast) {
  count = 0;
  initGlobals();
  initOtherGlobals && initOtherGlobals();

  //print("fixStm start");
  fixStm(ast);
  //print("fixStm succeeded");

  initCoreObjs();
  initOtherObjs && initOtherObjs();

  if (commonJSmode) { // create the exports object
    var e = new Aobj({}), eaddr = ++count;
    var eav = makeObjAval(eaddr), eavaddr = ++count;
    heap[eaddr] = e;
    heap[eavaddr] = eav;
    exports_object_av_addr = eavaddr;
    exports_object.obj = e;
  }
  labelStm(ast);
  //print("labelStm done");

  tagVarRefsStm[SCRIPT](ast, [], [], "toplevel");
  //print("tagrefsStm done");

  markConts(ast, undefined, undefined);
  //print("markconts done");

  try {
    //print("Done with preamble. Analysis starting.");
    evalToplevel(ast);
    //print("after cfa2");
    // print("ts: " + timestamp);
    // print("mbs: " + maxBucketSize);
    // print("cef/noSum: " + callsEvalFun + " " + noSum);
    // print("rethrows: " + rethrows + "\n");
    // aveq_lens.forEach(function(elm) {print(elm);});
    // dumpHeap("heapdump.txt");
  }
  catch (e) {
    // print("timestamp: " + timestamp +
    //       ", prot " + uprot + "(" + uprotNew + ")" +
    //       ", hvar " + uvar +
    //       ", rethrows " + rethrows); 
    // print(e.message);

    if (e.code === undefined) e.code = CFA_ERROR;
    throw e;
  }
}

// node, string, Array of string, cmd-line options -> Array of ctags
function getTags(ast, pathtofile, lines, options) {
  const REGEX_ESCAPES = { "\n": "\\n", "\r": "\\r", "\t": "\\t" };
  var tags = [];

  function regexify(str) {
    function subst(ch) {
      return (ch in REGEX_ESCAPES) ? REGEX_ESCAPES[ch] : "\\" + ch;
    }
    str || (str = "");
    return "/^" + str.replace(/[\\/$\n\r\t]/g, subst) + "$/";
  }

  if (options.commonJS) commonJSmode = true;
  // print(pathtofile);
  cfa2(ast);
  // print("Flow analysis done. Generating tags");

  if (exports_object.obj) {
    var eo = exports_object.obj;
    eo.forEachOwnProp(function (p) {
      var av = eo.getOwnExactProp(p);
      var tag = {};
      tag.name = /-$/.test(p) ? p.slice(0, -1) : p.slice(1);
      tag.tagfile = pathtofile;
      tag.addr = regexify(lines[exports_object.lines[p] - 1]);
      var type = av.toType();
      if (/(^<.*> function)|(^[^<>\|]*function)/.test(type))
        tag.kind = "f";
      else
        tag.kind = "v";
      tag.type = type;
      tag.module = options.module;
      tag.lineno = exports_object.lines[p];
      tags.push(tag);
    });
  }

  for (var addr in summaries) {
    var f = flags[addr];
    tags.push({ name : f.fname.name || "%anonymous_function",
                tagfile : pathtofile,
                addr : regexify(lines[f.lineno - 1]),
                kind : "f",
                type : funToType(f),
                lineno : f.lineno.toString()
              });
  }
  ast.varDecls.forEach(function(vd) {
    tags.push({ name : vd.name,
                tagfile : pathtofile,
                addr : regexify(lines[vd.lineno - 1]),
                kind : "v",
                type : heap[vd.addr].toType(),
                lineno : vd.lineno.toString()
              });
  });
  return tags;
}

// node -> boolean
// hacky test suite. Look in run-tests.js
function runtest(ast) {
  cfa2(ast);
  // find test's addr at the toplevel
  var testaddr, fds = ast.funDecls;
  for (var i = 0, len = fds.length; i < len; i++) 
    if (fds[i].fname.name === "test") {
      testaddr = fds[i].addr;
      break;
    }
  if (testaddr === undefined) throw new Error("malformed test");
  var type = summaries[testaddr].type;
  // print(type[0][1]);
  // print(type[1]);
  return aveq(type[0][1], type[1]);
}

exports.cfa2 = cfa2;
exports.runtest = runtest;
exports.getTags = getTags;

////////////////////////////////////////////////////////////////////////////////
//////////////    DATA DEFINITIONS FOR THE AST RETURNED BY JSPARSE  ////////////
////////////////////////////////////////////////////////////////////////////////

function walkExp(n) {

  switch (n.type){

    //nullary
  case NULL:
  case THIS:
  case TRUE:
  case FALSE:
    break;

  case IDENTIFIER:
  case NUMBER:
  case STRING:
  case REGEXP:
    // n.value
    break;

    //unary
  case DELETE:
  case VOID:
  case TYPEOF:
  case NOT:
  case BITWISE_NOT:
  case UNARY_PLUS: case UNARY_MINUS:
  case NEW:
  case GROUP: //parenthesized expr
    walkExp(n[0]); 
    break;

  case INCREMENT: case DECREMENT:
    // n.postfix is true or undefined
    walkExp(n[0]);
    break;

    //binary
  case CALL:
  case NEW_WITH_ARGS:
    walkExp(n[0]); 
    //n[1].type === LIST
    n[1].forEach(walkExp);
    break;

  case IN:
    walkExp(n[0]); // an exp which must eval to string
    walkExp(n[1]); // an exp which must eval to obj
    break;

  case DOT:
    walkExp(n[0]);
    walkExp(n[1]); // must be IDENTIFIER
    break;

  case BITWISE_OR: case BITWISE_XOR: case BITWISE_AND:
  case EQ: case NE: case STRICT_EQ: case STRICT_NE:
  case LT: case LE: case GE: case GT:
  case INSTANCEOF:
  case LSH: case RSH: case URSH:
  case PLUS: case MINUS: case MUL: case DIV: case MOD:
  case AND: case OR:
  case ASSIGN: // n[0].assignOp shows which op-and-assign operator we have here
  case INDEX: // property indexing  
    walkExp(n[0]);
    walkExp(n[1]);
    break;

    //ternary
  case HOOK:
    walkExp(n[0]);
    walkExp(n[1]);
    walkExp(n[2]);
    break;

    //variable arity
  case COMMA:
  case ARRAY_INIT: // array literal
    n.forEach(walkExp);
    break;

  case OBJECT_INIT:
    n.forEach(function(prop) { // prop.type === PROPERTY_INIT
      walkExp(prop[0]); // identifier, number or string
      walkExp(prop[1]);
    });
    break;

    //other
  case FUNCTION:
    // n.name is a string
    // n.params is an array of strings
    // n.functionForm === EXPRESSED_FORM
    walkStm(n.body);
    break;
  }
}

function walkStm(n) {
  switch (n.type) {

  case SCRIPT: 
  case BLOCK:
    n.forEach(walkStm);
    break;

  case FUNCTION:
    // n.name is a string
    // n.params is an array of strings
    // n.functionForm === DECLARED_FORM or STATEMENT_FORM
    // STATEMENT_FORM is for funs declared in inner blocks, like IF branches
    // It doesn't extend the funDecls of the script, bad!
    walkStm(n.body);
    break;

  case SEMICOLON:
    n.expression && walkExp(n.expression); 
    break;

  case IF:
    walkExp(n.condition);
    walkStm(n.thenPart);
    n.elsePart && walkStm(n.elsePart);
    break;
    
  case SWITCH:
    walkExp(n.discriminant);
    // a switch w/out branches is legal, n.cases is []
    n.cases.forEach(function(branch) {
      branch.caseLabel && walkExp(branch.caseLabel);
      // if the branch has no stms, branch.statements is an empty block
      walkStm(branch.statements);
    });
    break;

  case FOR: 
    if (n.setup) {
      if (n.setup.type === VAR || n.setup.type === CONST)
        walkStm(n.setup);
      else walkExp(n.setup);
    }
    n.condition && walkExp(n.condition);
    n.update && walkExp(n.update);
    walkStm(n.body);
    break;

  case FOR_IN:
    // n.varDecl may be used when there is a LET at the head of the for/in loop.
    walkExp(n.iterator);
    walkExp(n.object);
    walkStm(n.body);
    break;

  case WHILE:
  case DO:
    walkExp(n.condition);
    walkStm(n.body);
    break;

  case BREAK:
  case CONTINUE:
    // do nothing: n.label is just a name, n.target points back to ancestor
    break;

  case TRY:
    walkStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) { // clause.varName is a string
      clause.guard && walkExp(clause.guard);
      walkStm(clause.block);
    });
    n.finallyBlock && walkStm(n.finallyBlock);
    break;

  case THROW: 
    walkExp(n.exception);
    break;

  case RETURN:
    n.value && walkExp(n.value);
    break;
    
  case WITH:
    walkExp(n.object);
    walkStm(n.body);
    break;

  case LABEL:
    // n.label is a string
    walkStm(n.statement);
    break;

  case VAR: 
  case CONST: // variable or constant declaration
    // vd.name is a string
    // vd.readOnly is true for constants, false for variables
    n.forEach(function(vd) { walkExp(vd.initializer); });
    break;
  }
  return n;
}

////////////////////////////////////////////////////////////////////////////////
////////////    EVENT CLASSIFICATION FOR FIREFOX ADDONS    /////////////////////
////////////////////////////////////////////////////////////////////////////////

var eventClassif;
var chrome_obj_av_addr;

// make separate constructors for chrome and content objs, so that we can 
// distinguish them w/ instanceof
function Chrome(specialProps) { Aobj.call(this, specialProps); }
Chrome.prototype = new Aobj({});

function Content(specialProps) { Aobj.call(this, specialProps); }
Content.prototype = new Aobj({});

(function() {
  // Initializing functions are overriden here

  initOtherGlobals = function() { eventClassif = {total:0, analyzed:0}; };
  initOtherObjs = initDOMObjs;

  // almost identical to the original, the only change is for global variables
  function _tvre_nullary(n, innerscope, otherscopes) {
    if (n.type !== IDENTIFIER) return; 
    var boundvar, varname = n.name;
    // search var in innermost scope
    for (var i = innerscope.length - 1; i >= 0; i--) {
      boundvar = innerscope[i];
      if (boundvar.name === varname) {
        //print("stack ref: " + varname);
        n.kind = STACK;
        // if boundvar is a heap var and some of its heap refs get mutated,
        // we may need to update bindings in frames during the cfa.
        n.addr = boundvar.addr; 
        return;
      }
    }
    // search var in other scopes
    for (var i = otherscopes.length - 1; i >= 0; i--) {
      boundvar = otherscopes[i];
      if (boundvar.name === varname) {
        // print("heap ref: " + varname);
        n.kind = boundvar.kind = HEAP;
        n.addr = boundvar.addr;
        flags[boundvar.addr] = true;
        return;
      }
    }
    // var has no binder in the program
    if (commonJSmode && varname === "exports") {
      n.kind = HEAP;
      n.addr = exports_object_av_addr;
      var p = arguments[3]; // exported property name passed as extra arg
      if (p.type === IDENTIFIER)
        exports_object.lines[p.name] = p.lineno;
      return;
    }
    //print("global: " + varname + " :: " + n.lineno);
    n.type = DOT;
    var nthis = idNode({}, "global object");
    nthis.kind = HEAP;
    if (n.name === "addEventListener")
      nthis.addr = chrome_obj_av_addr;
    else 
      nthis.addr = global_object_av_addr;
    n.push(nthis);
    n.push(idNode({}, n.name + "-"));
  }

  tagVarRefsExp[NULLARY] = _tvre_nullary;

  function _ide_bin(n) {
    if (n.type === DOT && n[1].value === "addEventListener-") {
      n.addr = ++count;
      ++eventClassif.total;
      // result is an Array of four strings, describing the listener: 
      // event name: some specific name or unknown
      // attached on: chrome, content or any
      // originates from: chrome, content or any
      // status: safe or unsafe
      eventClassif[count] = {lineno:n.lineno,analyzed:false,result:undefined};
    }
    n.forEach(function(e) { initDeclsExp[opArity[e.type]](e); });
  }

  initDeclsExp[BINARY] = _ide_bin;
})();

function initDOMObjs() {

  function toThis(args) { return new Ans(args[0]); }

  // the whole DOM tree is modeled by 2 chrome and 1 content object
  var chr = new Chrome({}), chraddr = ++count, chrav = makeObjAval(chraddr);
  heap[chraddr] = chr;
  chrome_obj_av_addr = ++count;
  heap[chrome_obj_av_addr] = chrav;
  var chr2 = new Chrome({}), chr2addr = ++count, chr2av = makeObjAval(chr2addr);
  heap[chr2addr] = chr2;
  var con = new Content({}), conaddr = ++count, conav = makeObjAval(conaddr);
  heap[conaddr] = con;

  chr.updateProp("contentDocument-", conav);
  chr.updateProp("content-", chr2av);
  chr.updateProp("contentWindow-", chr2av);
  chr2.updateProp("document-", conav);
  con.updateProp("documentElement-", conav);

  ["firstChild-", "lastChild-", "nextSibling-"].forEach(
    function(pname) {
      chr.updateProp(pname, chrav);
      chr2.updateProp(pname, chr2av);
      con.updateProp(pname, conav);
    }
  );
  chr.updateProp("parentNode-", chrav);
  chr2.updateProp("parentNode-", chrav);
  con.updateProp("parentNode-", conav);

  ["getElementById", "appendChild", "removeChild", "createElement"].forEach(
    function(fname) {
      attachMethod(chr, fname, toThis, 1);
      attachMethod(con, fname, toThis, 1);
    }
  );

  // chrarr is for functions that normally return a Node list of chrome elms
  var chrarr = new Aobj({}), chrarraddr = ++count;
  var chrarrav = makeObjAval(chrarraddr);
  heap[chrarraddr] = chrarr;
  array_constructor([chrarrav], true);
  chrarr.updateNumProps(chrav);

  // conarr is for functions that normally return a Node list of content elms
  var conarr = new Aobj({}), conarraddr = ++count;
  var conarrav = makeObjAval(conarraddr);
  heap[conarraddr] = conarr;
  array_constructor([conarrav], true);
  conarr.updateNumProps(conav);

  function toNodeList(args) {
    if (args[0] instanceof Chrome) return chrarr; else return conarr;
  }

  chr.updateProp("childNodes-", chrarrav);
  chr2.updateProp("childNodes-", chrarrav);
  con.updateProp("childNodes-", conarrav);  

  [["querySelectorAll", 1], ["getElementsByClassName", 1],
   ["getElementsByAttribute", 2], ["getElementsByTagName", 1]].forEach(
     function(pair) {
       var p0 = pair[0], p1 = pair[1];
       attachMethod(chr, p0, toNodeList, p1);
       attachMethod(chr2, p0, toNodeList, p1);
       attachMethod(con, p0, toNodeList, p1);
     }
   );

  var go = heap[global_object_av_addr];
  go.updateProp("window-", chrav);
  go.updateProp("document-", chrav);
  go.updateProp("gBrowser-", chrav);

  function aEL(args, withNew, callNode) {
    // oldr can be undefined
    function evtjoin(oldr, newr) {
      if (oldr) {
        if (oldr[0] !== newr[0]) newr[0] = "unknown-";
        if (oldr[1] !== newr[1]) newr[1] = "any";
        if (oldr[2] !== newr[2]) newr[2] = "any";
        if (oldr[3] !== newr[3]) newr[3] = "unsafe";
      }
      return newr;
    }

    var evt = (args[1] && args[1].getStrLit()) || "unknown-";
    var ratorNode = callNode[0], ec, kind, r;

    if (!ratorNode) return new Ans(BOTTOM);
    ec = eventClassif[ratorNode.addr];
    if (!ec.analyzed) {
      ec.analyzed = true;
      ++eventClassif.analyzed;
    }
    kind = eventKinds[evt.slice(0,-1)];
    if (kind === XUL)
      r = [evt, "chrome", "chrome", "safe"];
    else {
      var numobjs = 0;
      args[0].forEachObj(function(o) {
        ++numobjs;
        if (o instanceof Chrome) {
          var r2 = [evt, "chrome", undefined, undefined];
          if (kind === NO_BUBBLE) {
            r2[2] = "chrome";
            r2[3] = "safe";
          }
          else if (kind === BUBBLE || evt === "unknown-" || 
                   args[4] /* listener for custom untrusted event */) {
            r2[2] = "any";
            r2[3] = "unsafe"
          }
          else { // listener for custom trusted event
            r2[2] = "chrome";
            r2[3] = "safe";
          }
          r = evtjoin(r, r2);
        }
        else if (o instanceof Content) {
          r = evtjoin(r, [evt, "content", "content", "unsafe"]);
        }
        else 
          r = evtjoin(r, [evt, "any", "any", "unsafe"]);
      });
      if (numobjs === 0) r = [evt, "any", "any", "unsafe"];
    }
    ec.result = evtjoin(ec.result, r);
    return new Ans(BOTTOM);
  }

  var aELaddr = ++count, aELav;
  heap[aELaddr] = new Aobj({proto : function_prototype_av,
                            fun : funToNode("addEventListener-", aEL, 3)});
  aELav = makeObjAval(aELaddr);

  // replace evalExp/DOT with the following function
  function _dot(n, fr) {
    var ans = evalExp[n[0].type](n[0], fr), avobj = ans.v.baseToObj();
    ans.thisav = avobj; // used by method calls
    if (n[1].name === "addEventListener-")
      ans.v = aELav;
    else {
      ans.v = avobj.getProp(n[1].name);
      //hideous hack for properties of chrome & content elms we don't know about
      if (aveq(ans.v, AUNDEF))
        avobj.forEachObj(function(o) {
          if (o instanceof Chrome || o instanceof Content) ans.v = avobj;
        });
    }
    return ans;
  }
  evalExp[DOT] = _dot;
}

const XUL = 0, BUBBLE = 1, NO_BUBBLE = 2;
var eventKinds = {
  click : BUBBLE,
  DOMAttrModified : BUBBLE,
  DOMNodeInserted : BUBBLE,
  DOMNodeRemoved : BUBBLE,
  load : NO_BUBBLE,
  mousedown : BUBBLE,
  submit : BUBBLE,
  TabClose : XUL,
  TabOpen : XUL,
  TabSelect : XUL
};

function classify_events(ast) {
  cfa2(ast);
  return eventClassif;
}

exports.classify_events = classify_events;
