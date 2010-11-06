// global variables can also be accessed as properties of the global object
function test(expected) {
  this.NaN = "foo";
  return NaN;
}

var numOrStr;
numOrStr = 0;
numOrStr = "";
test(numOrStr);


