method BinarySearch(a: array<int>, key: int) returns (n: int)
    requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
    ensures 0 <= n <= a.Length //+LLM
    ensures n < a.Length ==> a[n] >= key //+LLM
    ensures n > 0 ==> a[n-1] < key //+LLM
{
    var lo, hi := 0, a.Length;
    while lo < hi
        invariant 0 <= lo <= hi <= a.Length //+LLM
        invariant forall i :: 0 <= i < lo ==> a[i] < key //+LLM
        invariant forall i :: hi <= i < a.Length ==> a[i] >= key //+LLM
        // decreases hi - lo //+LLM
    {
        var mid := (lo + hi) / 2;
        if a[mid] < key {
            lo := mid + 1;
        } else {
            hi := mid;
        }
    }
    n := lo;
}