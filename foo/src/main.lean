import data.list.basic
import init.data.list.lemmas

open list

def atom := string

inductive lvalue 
| tt
| uu
| ff




structure rule :=
  (head : list atom)
  (pbody : list atom)
  (nbody : list atom)

def program := list rule


example : program := [
  rule.mk [] [] [],
  rule.mk [] [] [],
  rule.mk [] [] []]

example : rule :=
  { rule . head := [],
        pbody := [],
        nbody := [] } 


#check list.subset

structure I :=
  (T : list atom)
  (P : list atom)
  (subset : T ⊆ P)

section I
variable i : I
@[reducible] def eval (a : atom) : lvalue := 
  if a ∈ i.T then lvalue.tt else 
  if a ∈ i.P then lvalue.uu else lvalue.ff

def II : I :=
  have T : _ := ["a"],
  have Pplus : _ := ["b"],
  show I, begin 
    let P := T ++ Pplus,
    have subset : T ⊆ P := begin
      apply subset_append_of_subset_left,
      apply subset.refl,
    end,
    exact ⟨T, P, subset⟩
  end

end I

def OrAtom (A : list atom)

section rule
  variable r : rule
  def sat (i : I) : bool := 
    sorry
end rule