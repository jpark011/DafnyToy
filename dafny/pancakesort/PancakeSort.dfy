include "flip.dfy"
include "findmax.dfy"


method pancakeSort (a : array<int>)
  requires 0 < a.Length;
  modifies a;
  ensures forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j];
  ensures multiset(old(a[..])) == multiset(a[..]);
{
  var curr_size := a.Length;
  while (curr_size > 1)
    invariant 0 < curr_size <= a.Length;
    invariant forall i, j :: 0 <= i < curr_size <= j < a.Length ==> a[i] <= a[j]
    invariant forall i, j :: curr_size <= i <= j < a.Length ==> a[i] <= a[j];
    invariant multiset(old(a[..])) == multiset(a[..]);
    decreases curr_size;
  {
    var mi := findMax (a, curr_size);
    if (mi != curr_size - 1)
    {
      flip (a, mi);
      flip (a, curr_size -1);
    }
    curr_size := curr_size - 1;
  }
}
