function Sum(f: int ~> real, lo: int, hi: int): real
  requires lo <= hi
  requires forall i :: f.requires(i)
  reads f.reads
  decreases hi - lo
{
  if lo == hi then 0.0 else
    f(lo) + Sum(f, lo + 1, hi)
}