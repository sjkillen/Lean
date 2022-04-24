
import data.fintype.order
import data.nat.basic -- Some basic simps
import order.complete_lattice

inductive tv
| vtrue
| vundef
| vfalse
open tv

namespace tv
@[simp] def to_nat (a : tv) : ℕ := tv.cases_on a 3 2 1
@[simp] lemma tv_unnat_eq {a b : tv} : (tv.to_nat a) = (tv.to_nat b) <-> a = b :=  begin
    split, all_goals { assume h, cases a; cases b; simp at |- h; contradiction },
end


@[reducible] def le (a b : tv) : Prop := nat.le (tv.to_nat a) (tv.to_nat b)
@[reducible] def lt (a b : tv) : Prop := nat.lt (tv.to_nat a) (tv.to_nat b)
instance : has_le tv := ⟨le⟩
instance : has_lt tv := ⟨lt⟩

-- Lemmas for the linear order on tv
-- that uses the mapping to_nat and the standard linear ordering on nat
@[refl] lemma le_refl (a : tv) : a <= a := nat.le_refl (tv.to_nat a)
@[trans] lemma le_trans {n m k : tv} (h1 : n ≤ m) : m ≤ k → n ≤ k := λ h2, nat.le_trans h1 h2
lemma le_antisymm {n m : tv} (h1 : n ≤ m) : m ≤ n → n = m :=  λ h2, tv_unnat_eq.mp (nat.le_antisymm h1 h2)
lemma le_total {m n : tv} : m ≤ n ∨ n ≤ m := nat.le_total
lemma lt_iff_le_not_le {m n : tv} : m < n ↔ (m ≤ n ∧ ¬ n ≤ m) := nat.lt_iff_le_not_le 
instance decidable_lt : ∀ a b : tv, decidable (a < b) := λ a b, nat.decidable_lt (tv.to_nat a) (tv.to_nat b)
instance decidable_le : ∀ a b : tv, decidable (a ≤ b):= λ a b, nat.decidable_le (tv.to_nat a) (tv.to_nat b)
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

-- There are finite truth values
instance fintype : fintype tv := {
  elems := {vfalse, vundef, vtrue},
  complete := λ a, by { cases a; simp }}



-- Not sure why mathlib doesn't define this for linearly ordered fintypes
-- This proof is so stupid, there has to be a better way...
instance bounded_order : bounded_order tv := {
  top := vtrue,
  le_top := begin
    assume a,
    have h1 : a <= a := @nat.less_than_or_equal.refl a.to_nat,
    have h2 := nat.less_than_or_equal.step h1,
    have h3 := nat.less_than_or_equal.step h2,
    cases a,
    all_goals { finish },
  end,
  bot := vfalse,
  bot_le := begin
    assume a,
    have h1 := @nat.less_than_or_equal.refl vfalse.to_nat,
    have h2 := nat.less_than_or_equal.step h1,
    have h3 := nat.less_than_or_equal.step h2,
    cases a,
    all_goals { finish },
  end,
}


@[reducible]
noncomputable instance complete_linear_order : complete_linear_order tv := fintype.to_complete_linear_order tv

@[reducible]
noncomputable instance complete_lattice : complete_lattice tv := complete_linear_order.to_complete_lattice tv


end tv


def atom := ℕ

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
