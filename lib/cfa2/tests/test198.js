// WITH: L-value
function test(expected) {
  var o = {x : 1};
  with (o) { x = "asdf"; }
  return o.x
}

var numOrStr = 0;
numOrStr = "asdf";
test(numOrStr);
