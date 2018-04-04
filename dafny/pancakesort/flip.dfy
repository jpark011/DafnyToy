// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array<int>, num: int)
  requires 0 <= num < a.Length;
  modifies a;
  ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k]);
  ensures forall k :: num < k < a.Length ==> a[k] == old(a[k]);
{
  var tmp:int;

  var i := 0;
  var j := num;
  while (i < j)
    invariant 0 <= i <= j <= num;
    // left
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[num-k]);
    // center
    invariant forall k :: j < k < num ==> a[k] == old(a[num-k]);
    // right
    invariant forall k :: j < k <= num ==> a[k] == old(a[k]);
    invariant forall k :: num < k < a.Length ==> a[k] == old(a[k]);
    decreases j - i;
  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
}
