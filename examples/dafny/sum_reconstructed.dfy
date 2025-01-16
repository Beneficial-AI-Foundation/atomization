function Sum(f: int ~> real, lo: int, hi: int): real
   requires lo <= hi
   requires forall i :: lo <= i < hi ==> f.requires(i)
   reads set i, o | lo <= i < hi && o in f.reads(i) :: o
   decreases hi - lo
{
  if lo == hi then 0.0 else
    f(lo) + Sum(f, lo + 1, hi)
}
