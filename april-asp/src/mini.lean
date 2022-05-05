


def recurses : list nat -> nat
| [] := 0
| (hd::tl) := recurses tl


example {hd : nat} {tl : list nat} : recurses (hd::tl) = 0 := begin
  change recurses tl = 0,
  
end