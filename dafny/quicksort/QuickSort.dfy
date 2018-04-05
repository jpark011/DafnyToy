include "part.dfy"


method qsort(a:array<int>, l:nat, u:nat)
  requires a != null;
  requires l <= u < a.Length;
  modifies a;

  ensures sorted_between(a, l, u+1);
{
  var pivot = partition(a, l, u);
  // left
  qsort(a, l, pivot - 1);
  // right
  qsort(a, pivot + 1, u)
}
