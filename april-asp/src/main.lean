import data.nat.basic -- Some basic simps
-- This is here so I don't forget how to trace
-- set_option trace.simplify.rewrite true

#check nat.one_ne_zero

def atom := nat
inductive tv
| vtrue
| vundef
| vfalse
@[simp] def tv_nat (a : tv) : ℕ := tv.cases_on a 3 2 1
@[simp] lemma tv_unnat_eq {a b : tv} : (tv_nat a) = (tv_nat b) <-> a = b :=  begin
    split, all_goals { assume h, cases a; cases b; simp at |- h; contradiction },
end

@[reducible] def tv_le (a b : tv) : Prop := nat.le (tv_nat a) (tv_nat b)
@[reducible] def tv_lt (a b : tv) : Prop := nat.lt (tv_nat a) (tv_nat b)
instance : has_le tv := ⟨tv_le⟩
instance : has_lt tv := ⟨tv_lt⟩
namespace tv
@[refl] lemma le_refl (a : tv) : a <= a := nat.le_refl (tv_nat a)
@[trans] lemma le_trans {n m k : tv} (h1 : n ≤ m) : m ≤ k → n ≤ k := λ h2, nat.le_trans h1 h2
lemma le_antisymm {n m : tv} (h1 : n ≤ m) : m ≤ n → n = m :=  λ h2, tv_unnat_eq.mp (nat.le_antisymm h1 h2)
lemma le_total {m n : tv} : m ≤ n ∨ n ≤ m := nat.le_total
lemma lt_iff_le_not_le {m n : tv} : m < n ↔ (m ≤ n ∧ ¬ n ≤ m) := nat.lt_iff_le_not_le 
instance decidable_lt : ∀ a b : tv, decidable (a < b) := λ a b, nat.decidable_lt (tv_nat a) (tv_nat b)
instance decidable_le : ∀ a b : tv, decidable (a ≤ b):= λ a b, nat.decidable_le (tv_nat a) (tv_nat b)
instance decidable_eq : decidable_eq tv := λ a b, by { rw <- tv_unnat_eq, apply nat.decidable_eq }
instance linear_order : linear_order tv :=
{ le := tv_le,
  le_refl := tv.le_refl,
  le_trans := @tv.le_trans,
  le_antisymm := @tv.le_antisymm,
  le_total := @tv.le_total,
  lt := tv_lt,
  lt_iff_le_not_le := @tv.lt_iff_le_not_le,
  decidable_le               := tv.decidable_le,
  -- These fields are optional but easy enough to define
  decidable_lt               := tv.decidable_lt,
  decidable_eq               := tv.decidable_eq 
}
end tv
-- These two can be used interchangeably
example (a b : tv) (h : a <= b) : tv_nat a <= tv_nat b := h






def I := atom -> tv
inductive I_less_than_or_equal (i1 : I) (i2 : I) : Prop
| mk (p : Π a : atom, (i1 a) <= (i2 a)) : I_less_than_or_equal
instance : has_le I := ⟨I_less_than_or_equal⟩
inductive I_less_than (i1 : I) (i2 : I) : Prop
| mk (p : i1 <= i2) (q : ∃a : atom, (i1 a) < (i2 a)) : I_less_than
instance : has_lt I := ⟨I_less_than⟩ 
namespace I
@[refl] lemma le_refl (i : I) : i <= i := I_less_than_or_equal.mk (λ a : atom, tv.le_refl (i a))
end I



def foo [preorder ℕ] : Prop := sorry


#check min

structure Rule :=
  (head : atom)
  (pbody : list atom)
  (nbody : list atom)

namespace Rule
  def atoms (self : Rule) : list atom :=
    self.head :: (self.pbody ++ self.nbody)
  -- Body of a rule is undefined w.r.t.
  structure body_eval (self : Rule) (i : I)

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
