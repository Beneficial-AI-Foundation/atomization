const MAX_INT := 0x7fffffff

lemma TetrahedralLemma(n: nat)
  requires n >= 0
  requires n * (n + 1) * (n + 2) <= 6 * MAX_INT
  ensures (n * (n + 1) * (n + 2)) / 6 == 
          ((n * (n + 1)) / 2) + ((n - 1) * n * (n + 1)) / 6
  decreases n
{
  // Lemma helps prove the relationship
}

function Tetrahedral(n: nat): nat
  requires n >= 0
  requires n * (n + 1) * (n + 2) <= 6 * MAX_INT //+LLM
  ensures Tetrahedral(n) >= 0 //+LLM
  ensures Tetrahedral(n) == (n * (n + 1) * (n + 2)) / 6 //+LLM
  ensures n > 0 ==> Tetrahedral(n) == Triangular(n) + Tetrahedral(n-1) //+LLM
  decreases n
{
  if n == 0 then
    0
  else 
    Triangular(n) + Tetrahedral(n-1)
}

function Triangular(n: nat): nat
  requires n >= 0
  requires n * (n + 1) <= 2 * MAX_INT //+LLM
  ensures Triangular(n) == n * (n + 1) / 2
{
  n * (n + 1) / 2
}