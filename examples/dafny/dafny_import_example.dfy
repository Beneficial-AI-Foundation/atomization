module A {
  const a := 10
  const z := 10
}
module B {
  import opened Z = A // includes a, declares Z
  const b := Z.a // OK
}
module C {
  import opened B // includes b, Z, but not a
  method m() {
    //assert b == a; // error: a is not known
    //assert b == B.a; // error: B.a is not valid
    //assert b == A.a; // error: A is not known
    assert b == Z.a; // OK: module Z is known and includes a
  }
}