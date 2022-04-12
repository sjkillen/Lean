import data.list.basic
import init.data.list.lemmas

import util


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

  @[simp, reducible] def U : list atom :=
    filter (λ x, x ∉ i.T) i.P

  @[simp, reducible] def eval (a : atom) : lvalue := 
    if a ∈ i.T then lvalue.tt else 
    if a ∈ i.P then lvalue.uu else lvalue.ff

  def for (i : I) (a : list atom) : I :=
    begin
      let T₂ := (filter (λ x, x ∈ a) i.T),
      let P₂ := (filter (λ x, x ∈ a) i.P),
      
    end

  -- def eval_I (a : list atom) :

  -- @[simp, reducible] def eval_or (a : list atom) : lvalue := 


  private def I_from_disjoint (T : list atom) (PwithoutT : list atom) : I :=
    begin
      let P := T ++ PwithoutT,
      have subset : T ⊆ P := begin
        apply subset_append_of_subset_left,
        apply subset.refl,
      end,
      exact ⟨T, P, subset⟩
    end



end I

section rule
  variable r : rule
  def sat (i : I) : bool := 
    sorry
end rule