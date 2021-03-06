// returns an index of the largest element of array 'a' in the range [0..n)
method findMax (a : array<int>, n : int) returns (r:int)
  requires 0 < n <= a.Length
  ensures 0 <= r < n;
  ensures forall i :: 0 <= i < n ==> a[i] <= a[r];
{
  var mi;
  var i;
  mi := 0;
  i := 0;
  while (i < n)
    invariant 0 <= i <= n;
    invariant 0 <= mi < n;
    invariant forall k :: 0 <= k < i ==> a[k] <= a[mi];
    decreases n - i;
  {
    if (a[i] > a[mi])
    { mi := i; }
    i := i + 1;
  }
  return mi;
}
