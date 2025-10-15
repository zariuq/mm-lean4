import Batteries.Data.Array.Lemmas

example {α} [Inhabited α] (a : Array α) (k : Fin a.size) : a[k.val]! = a[k] := by
  rfl

#check @Array.get!
#print Array.get!
