
import data.fintype.order
import data.nat.basic -- Some basic simps
import order.complete_lattice
-- This is here so I don't forget how to trace
-- set_option trace.simplify.rewrite true
open list

-- Most of the time noncomputable traces back to set.fintype, which assumes that we can decide whether an element is in a set.

set_option trace.simplify.rewrite true



def atom := nat
instance : inhabited atom := nat.inhabited
inductive tv
| vtrue
| vundef
| vfalse
open tv
-- Negation of truth values is same as FOL except undefined maps to undefined
-- Defined for a tv, v to use notations -v
@[simp] def tv_nat (a : tv) : ℕ := tv.cases_on a 3 2 1
@[simp] lemma tv_unnat_eq {a b : tv} : (tv_nat a) = (tv_nat b) <-> a = b :=  begin
    split, all_goals { assume h, cases a; cases b; simp at |- h; contradiction },
end

namespace tv
@[reducible] def le (a b : tv) : Prop := nat.le (tv_nat a) (tv_nat b)
@[reducible] def lt (a b : tv) : Prop := nat.lt (tv_nat a) (tv_nat b)
instance : has_le tv := ⟨le⟩
instance : has_lt tv := ⟨lt⟩
@[refl] lemma le_refl (a : tv) : a <= a := nat.le_refl (tv_nat a)
@[trans] lemma le_trans {n m k : tv} (h1 : n ≤ m) : m ≤ k → n ≤ k := λ h2, nat.le_trans h1 h2
lemma le_antisymm {n m : tv} (h1 : n ≤ m) : m ≤ n → n = m :=  λ h2, tv_unnat_eq.mp (nat.le_antisymm h1 h2)
lemma le_total {m n : tv} : m ≤ n ∨ n ≤ m := nat.le_total
lemma lt_iff_le_not_le {m n : tv} : m < n ↔ (m ≤ n ∧ ¬ n ≤ m) := nat.lt_iff_le_not_le 
instance decidable_lt : ∀ a b : tv, decidable (a < b) := λ a b, nat.decidable_lt (tv_nat a) (tv_nat b)
instance decidable_le : ∀ a b : tv, decidable (a ≤ b):= λ a b, nat.decidable_le (tv_nat a) (tv_nat b)
instance decidable_eq : decidable_eq tv := λ a b, by { rw <- tv_unnat_eq, apply nat.decidable_eq }
instance fintype : fintype tv := {
  elems := {vfalse, vundef, vtrue},
  complete := λ a, by { cases a; simp }}
instance linear_order : linear_order tv :=
{ le := le,
  le_refl := tv.le_refl,
  le_trans := @tv.le_trans,
  le_antisymm := @tv.le_antisymm,
  le_total := @tv.le_total,
  lt := lt,
  lt_iff_le_not_le := @tv.lt_iff_le_not_le,
  decidable_le               := tv.decidable_le,
  -- These fields are optional but easy enough to define
  decidable_lt               := tv.decidable_lt,
  decidable_eq               := tv.decidable_eq }
@[simp, reducible] def neg (v : tv) : tv := tv.cases_on v tv.vfalse tv.vundef tv.vtrue
instance : has_neg tv := ⟨neg⟩ 
@[simp, reducible] def conj (a b : tv) := min a b
@[simp, reducible] def disj (a b : tv) := max a b
-- instance : has_inf tv := ⟨conj⟩
-- instance : has_sup tv := ⟨disj⟩
-- instance : has_bot tv := ⟨vfalse⟩
-- instance : has_top tv := ⟨vtrue⟩

-- class semilattice_sup (α : Type u) extends has_sup α, partial_order α :=
-- (le_sup_left : ∀ a b : α, a ≤ a ⊔ b)
-- (le_sup_right : ∀ a b : α, b ≤ a ⊔ b)
-- (sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c)


-- variable [lo : complete_lattice tv]
-- def foo [lo : complete_lattice tv] : Prop := true
-- #check @linear_order.to_lattice tv lo

-- -- This works
-- lemma le_sup_left (a b : tv) : a <= a ⊔ b := by { simp }
-- -- SO why shouldn't this?
-- lemma le_sup_left_2 [lo : linear_order tv] [sup : has_sup tv] (a b : tv) : a <= a ⊔ b := by { simp }
-- lemma le_sup_right (a b : tv) : b <= a ⊔ b := by { simp }
-- lemma sup_le (a b c : tv) : a ≤ c → b ≤ c → a ⊔ b ≤ c := by { simp, exact and.intro }

-- -- TODO look into this
-- #check linear_order.to_distrib_lattice

-- -- Problem here is that it can't recognize it as ⊔ 
-- instance : semilattice_sup tv := {
-- le_sup_left := le_sup_left,
-- le_sup_right := le_sup_right,
-- sup_le := sup_le,
-- sup := λ a b, a ⊔ b,
-- ..lo  }



-- #check complete_lattice


end tv
-- Logical conjunction of a list of truth values
-- TODO maybe use ⋀ syntax 
def tv_conj (l : list tv) : tv := foldl tv.conj tv.vtrue l
-- Logical disjunction of a list of truth values
def tv_disj (l : list tv) : tv := foldl tv.disj tv.vfalse l
-- Logical complement of a list of truth values
def tv_neg (l : list tv) : list tv := map tv.neg l



def foo { α : Type } [fintype α] (S : set α) : :=


-- Probably don't care about this but maybe come back to it when I know how to deal with it better
instance {a : tv} {S : set tv} : decidable (a ∈ S) := 
@[reducible] noncomputable def tv_set_to_list (a : set tv) : list tv :=
  (if vfalse ∈ a then [vfalse] else []) ++
  (if vundef ∈ a then [vundef] else []) ++
  (if vtrue ∈ a then [vtrue] else [])
  


#check fintype.to_complete_linear_order

instance lattice_tv : lattice tv := @linear_order.to_lattice tv tv.linear_order
-- instance : lattice tv := lattice_tv
instance complete_lattice_tv : complete_lattice tv := {
  Sup := sorry,
  Sup_le := sorry,
  le_Sup := sorry,
  Inf := sorry,
  Inf_le := sorry,
  le_Inf := sorry,
  top := sorry,
  bot := sorry,
  le_top := sorry,
  bot_le := sorry,
  ..lattice_tv,
}


#check set.fintype

-- These two can be used interchangeably
example (a b : tv) (h : a <= b) : tv_nat a <= tv_nat b := h

def I := atom -> tv

structure I_less_than_or_equal  (i1 : I) (i2 : I) : Prop :=
  (p : Π a : atom, (i1 a) <= (i2 a))

instance : has_le I := ⟨I_less_than_or_equal⟩
structure I_less_than (i1 : I) (i2 : I) : Prop :=
  (p : i1 <= i2) (q : ∃a : atom, (i1 a) < (i2 a))
instance : has_lt I := ⟨I_less_than⟩ 
lemma I_not_lt_exists {i1 i2 : I} (h : ¬i1 <= i2) : ∃ a : atom, (i2 a) < (i1 a) := begin
  by_contradiction exis,
  rw not_exists at exis,
  -- Not sure why I can't write simp as `rw not_lt at exis`
  -- not_lt relies on tv.linear_order so it's probably doing the conversion but not tracing it
  simp at exis,
  have le : i1 <= i2 := ⟨ exis ⟩,
  exact h le,
end

namespace I
def le (i1 i2 : I) := I_less_than_or_equal i1 i2
def lt (i1 i2 : I) := I_less_than i1 i2
@[refl] lemma le_refl (i : I) : i <= i := ⟨λ a, tv.le_refl (i a)⟩ 
@[trans] lemma le_trans {a b c : I} (h1 : a ≤ b) : b ≤ c → a ≤ c := λ h2, ⟨λ a, tv.le_trans (h1.p a) (h2.p a)⟩
lemma le_antisymm {n m : I} (h1 : n <= m) : m <= n -> n = m := λ h2, funext (λ a : atom, tv.le_antisymm (h1.p a) (h2.p a))
lemma lt_iff_le_not_le {a b : I} : a < b ↔ (a ≤ b ∧ ¬ b ≤ a) := iff.intro
  (λ l, begin
    split, exact l.p,
    by_contradiction p,
    cases l.q with w kk,
    exact ((lt_iff_le_not_le.mp kk).right) (p.p w) end)
  (λ r, begin
    split, exact r.left,
    exact I_not_lt_exists r.right,
  end)
instance partial_order : partial_order I :=
{ le := le,
  lt := lt,
  le_refl := le_refl,
  le_trans := @le_trans,
  le_antisymm := @le_antisymm,
  lt_iff_le_not_le := @lt_iff_le_not_le }
def eval (self : I) (atoms : list atom) : list tv := map self atoms
end I


structure Rule :=
  (head : atom)
  (pbody : list atom)
  (nbody : list atom)
namespace Rule
  def atoms (self : Rule) : list atom :=
    self.head :: (self.pbody ++ self.nbody)
  def eval_pbody (self : Rule) (i : I) : tv := tv_conj (i.eval self.pbody) 
  def eval_nbody (self : Rule) (i : I) : tv := tv_conj (tv_neg (i.eval self.nbody))
  def eval_body (self : Rule) (i : I) : tv := tv.conj (self.eval_pbody i) (self.eval_nbody i)
  def eval_head (self : Rule) (i : I) : tv := i self.head
  structure satisfied (r : Rule) (i : I) : Prop :=
    (p : r.eval_body i <= r.eval_head i)
end Rule

def Program := list Rule
instance : has_mem Rule Program := ⟨@list.mem Rule⟩ 
namespace Program
  structure model (self : Program) (i : I) : Prop :=
    (p : ∀r ∈ self, Rule.satisfied r i)
  structure stable_model (self : Program) (i : I) : Prop :=
    (m : self.model i)
    (p : ∀ii <= i, ¬(self.model i))
end Program









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
