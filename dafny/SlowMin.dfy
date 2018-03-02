function min(x:nat, y:nat) : nat {
  if (x < y) then x else y
}

method slow_min(a: nat, b:nat) returns (z:nat)
  ensures z == min(a, b);
{
  var x := a;
  var y := b;
  z := 0;
  while (x != 0 && y != 0)
    invariant true
    decreases 0
  {
    x := x - 1;
    y := y - 1;
    z := z + 1;
  }
}
