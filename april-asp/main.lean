open list

def Atom := nat

structure I :=
  (F : list Atom)
  (U : list Atom)
  (T : list Atom)

structure Rule :=
  (head : Atom)
  (pbody : list Atom)
  (nbody : list Atom)

namespace Rule
  def atoms (self : Rule) : list Atom :=
    self.head :: (self.pbody ++ self.nbody)
  -- Body of a rule is undefined w.r.t.
  structure body_possible (self : Rule) (i : I)
    (p : self.pbody ⊆ ())
  inductive body_undef (self : Rule) (i : I)
    | pbody (a : self.pbody ⊆ i.U)
    | twice : body_undef
end Rule


def rules_atoms (rules : list Rule) : list Atom :=
  foldl (λ l r, l ++ r) [] (map (λ r : Rule, r.atoms) rules)




structure State :=
  -- Rules that have not been applied
  -- atoms_* will not generate a conflict with these rules
  (rules_off : list Rule)
  (rules_on : list Rule)
  -- Atoms that haven't committed a value yet
  -- No rule in rules_on depends on these atoms
  (atoms_off : list Atom)
  -- Atoms that have been committed to false
  -- Used in the nbody of some rule in rules_on
  (atoms_false : list Atom)
  -- Same as atoms_false but appears in the head of a rule and is undefined
  (atoms_undef : list Atom)
  -- Same as atoms_undef but for true atoms 
  (atoms_true : list Atom)

namespace State
  def apply_rule (self : State) : Prop := sorry
  def into_I (self : State) : I :=
    I.mk self.atoms_false self.atoms_undef self.atoms_true
end State


structure Program :=
  (rules : list Rule)

namespace Program
  def into_state (self : Program) : State :=
    State.mk self.rules [] (rules_atoms self.rules) [] [] []
end Program



#check list.has_subset

open list

variable {α : Type}
instance : decidable (has_subset (list α)) := sorry

#reduce (if [1, 1] ⊆ [1] then 42 else 13)
