function Sum(i: nat, j: nat): nat
  requires i >= 0
  requires j >= 0
  ensures Sum(i, j) == i + j
{
  i + j
}

  // Helper function to compute triangular numbers
function Triangular(n: nat): nat
  requires n >= 0
  ensures Triangular(n) == n * Sum(1, n) / 2
{
  if n == 0 then
    0
  else
    n * Sum(1, n) / 2
}

function Tetrahedral(n: nat): nat
  requires n >= 0
  ensures n == 0 ==> Tetrahedral(n) == 0
  ensures n > 0 ==> Tetrahedral(n) == Triangular(n) + Tetrahedral(n-1)
{
    if n == 0 then
        0
    else 
        Triangular(n) + Tetrahedral(n-1)
}

