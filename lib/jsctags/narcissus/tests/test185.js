// unsound. Need to merge string properties in evalLval/_index
function test(expected) {
  var o = {a : ""}, x = "asdf";
  x = "a";
  o[x] = 0;
  return o.a;
}

test("");
