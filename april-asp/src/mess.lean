
import data.setoid.basic -- Not needed, reference only
import data.nat.basic -- Some basic simps
import order.complete_lattice
-- This is here so I don't forget how to trace
-- set_option trace.simplify.rewrite true
open list

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
instance : has_inf tv := ⟨conj⟩
instance : has_sup tv := ⟨disj⟩
instance : has_bot tv := ⟨vfalse⟩
instance : has_top tv := ⟨vtrue⟩




-- This works
lemma le_sup_left  (a b : tv) : a <= a ⊔ b := begin
apply le_sup_iff.mpr,
left,
apply le_refl,
end
-- SO why shouldn't this?
lemma le_sup_left_2 [lo : linear_order tv] [sup : has_sup tv] (a b : tv) : a <= a ⊔ b := begin

end