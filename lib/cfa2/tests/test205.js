// WITH: rewrite for/in
function test(expected) {
  var o = {x:1}, o2 = {"asdf" : 1};
  with (o) {
    for (x in o2) ;
  }
  return o.x;
}

var numOrStr = 0;
numOrStr = String();
test(numOrStr);
