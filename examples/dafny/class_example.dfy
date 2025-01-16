class A {
  var i: int
  var x0: int
  var x1: int
  var x2: int
  var x3: int
  var x4: int
  method M()
    modifies this
    ensures unchanged(`x0) && unchanged(`x1) && unchanged(`x2) && unchanged(`x3) && unchanged(`x4)
  { i := i + 1; }
}

class B {
  var i: int
  var x0: int
  var x1: int
  var x2: int
  var x3: int
  var x4: int
  method M()
    modifies `i
  { i := i + 1; }
  
  method N()
    modifies `i
  { i := i + 2; }
}