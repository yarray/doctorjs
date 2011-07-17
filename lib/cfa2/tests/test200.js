// not shadow by var
function test(expected) {
  var o = {x:1};
  with (o) {
    var x = "asdf";
    return x;
  }
}

var numOrStr = 0;
numOrStr = "asdf";
test(numOrStr);
