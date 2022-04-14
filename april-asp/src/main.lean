import data.finset

#check finset

--fintype
open list

def atom := nat

inductive tv
| vtrue
| vundef
| vfalse

def tv_nat (a : tv) : ℕ := tv.cases_on a 3 2 1
@[reducible] def tv_le (a b : tv) : Prop := nat.le (tv_nat a) (tv_nat b)
@[reducible] def tv_lt (a b : tv) : Prop := nat.lt (tv_nat a) (tv_nat b)
instance : has_le tv := ⟨tv_le⟩
instance : has_lt tv := ⟨tv_lt⟩ 

structure I (d : finset atom) :=
  (e : atom -> tv)

inductive I_lte : Π d : finset atom, (I d) -> (I d) -> Prop
| [] _ _ : I_lte


def f (a : finset ℕ) : finset ℕ := a

variable f : finset

#reduce f {1,2,3, 3}


inductive atom_list
| nil
| cons (hd : atom) (rst : list atom) (inv : atom > (head))


open nat







inductive I_less_than_or_equal (a : I) : I -> Prop
| refl : I_less_than_or_equal a


def I_gt_I (i1 i2 : I) (gt : ∀ a : atom, (i1 a) >= (i2 a)) : Prop := sorry


structure Rule :=
  (head : atom)
  (pbody : list atom)
  (nbody : list atom)

namespace Rule
  def atoms (self : Rule) : list atom :=
    self.head :: (self.pbody ++ self.nbody)
  -- Body of a rule is undefined w.r.t.
  structure body_possible (self : Rule) (i : I)
    (p : self.pbody ⊆ ())
  inductive body_undef (self : Rule) (i : I)
    | pbody (a : self.pbody ⊆ i.U)
    | twice : body_undef
end Rule


def rules_atoms (rules : list Rule) : list atom :=
  foldl (λ l r, l ++ r) [] (map (λ r : Rule, r.atoms) rules)




structure State :=
  -- Rules that have not been applied
  -- atoms_* will not generate a conflict with these rules
  (rules_off : list Rule)
  (rules_on : list Rule)
  -- atoms that haven't committed a value yet
  -- No rule in rules_on depends on these atoms
  (atoms_off : list atom)
  -- atoms that have been committed to false
  -- Used in the nbody of some rule in rules_on
  (atoms_false : list atom)
  -- Same as atoms_false but appears in the head of a rule and is undefined
  (atoms_undef : list atom)
  -- Same as atoms_undef but for true atoms 
  (atoms_true : list atom)

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
