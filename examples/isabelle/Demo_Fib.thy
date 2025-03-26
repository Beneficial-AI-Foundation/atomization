theory Demo_Fib
imports Main
begin

text "The code in this file is from https://isabelle.in.tum.de/doc/codegen.pdf" 

section "The specification for Fibonacci"

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0" |
  "fib (Suc 0) = Suc 0" |
  "fib (Suc (Suc n)) = fib n + fib (Suc n)"

definition fib_step :: "nat  \<Rightarrow> nat \<times> nat" where
  "fib_step n = (fib (Suc n), fib n)"

section "The proofs for the correctness of the implementation wrt the specification"

lemma [code]:
"fib_step 0 = (Suc 0, 0)"
"fib_step (Suc n) = (let (m, q) = fib_step n in (m + q, m))"
  by (simp_all add: fib_step_def )

lemma fib [code]:
"fib 0 = 0"
"fib (Suc n) = fst (fib_step n)"
  by (simp_all add: fib_step_def )

section "The executable code for Fibonacci is generated"

export_code
  fib
  in Haskell
end