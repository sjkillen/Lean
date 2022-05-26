/-
Defines truth values, atoms and interpretations
Defines the orderings for these types and provides mathlib instances for complete_lattices
Most of this file is uninterestingexcept for the first three definitions
Interpretations here are not bound to a particular program so most operations are undecidable
For a more restricted interpretation, see program.lean
-/ 

import data.fintype.order
import data.nat.basic -- Some basic simps
import order.complete_lattice
open list

-- set_option trace.simplify.rewrite true

inductive tv
| vtrue
| vundef
| vfalse
open tv
def atom := ℕ
instance : inhabited atom := nat.inhabited
def I := atom -> tv

namespace tv
  @[simp] def to_nat (a : tv) : ℕ := tv.cases_on a 3 2 1
  lemma to_nat.inj : function.injective to_nat := λ a b eq, begin
    cases a; cases b,
    any_goals {refl}, all_goals {simp at eq, contradiction},
  end
  @[simp] lemma tv_unnat_eq {a b : tv} : (tv.to_nat a) = (tv.to_nat b) <-> a = b :=  begin
      split, all_goals { assume h, cases a; cases b; simp at |- h; contradiction },
  end

  instance linear_order : linear_order tv := linear_order.lift tv.to_nat tv.to_nat.inj

  -- There are finite truth values
  instance fintype : fintype tv := {
    elems := {vfalse, vundef, vtrue},
    complete := λ a, by { cases a; simp }}

  def top : tv := vtrue
  lemma le_top (a : tv) : a <= tv.top := begin
      have h1 : a <= a := @nat.less_than_or_equal.refl a.to_nat,
      have h2 := nat.less_than_or_equal.step h1,
      have h3 := nat.less_than_or_equal.step h2,
      cases a,
      all_goals { finish },
  end
  def bot : tv := vfalse
  lemma bot_le (a : tv) : tv.bot <= a := begin
      have h1 := @nat.less_than_or_equal.refl vfalse.to_nat,
      have h2 := nat.less_than_or_equal.step h1,
      have h3 := nat.less_than_or_equal.step h2,
      cases a,
      all_goals { finish },
  end
  -- Not sure why mathlib doesn't define this for linearly ordered fintypes
  -- This proof is so stupid, there has to be a better way...
  instance bounded_order : bounded_order tv := {
    top := top,
    le_top := le_top,
    bot := bot,
    bot_le := bot_le,
  }
  @[reducible]
  noncomputable instance complete_linear_order : complete_linear_order tv := fintype.to_complete_linear_order tv
  @[reducible]
  noncomputable instance complete_lattice : complete_lattice tv := complete_linear_order.to_complete_lattice tv
  def sup := @max tv
  instance has_sup : has_sup tv := ⟨tv.sup⟩
  def inf := @min tv
  instance has_inf : has_inf tv := ⟨tv.inf⟩
  @[reducible] 
  noncomputable def Sup := tv.complete_lattice.Sup
  @[reducible] 
  noncomputable instance has_Sup : has_Sup tv := ⟨tv.Sup⟩
  @[reducible] 
  noncomputable def Inf := tv.complete_lattice.Inf
  @[reducible] 
  noncomputable instance has_Inf : has_Inf tv := ⟨tv.Inf⟩
end tv

namespace atom
  instance decidable_eq : decidable_eq atom := nat.decidable_eq
end atom


namespace I
  structure less_than_or_equal  (i1 : I) (i2 : I) : Prop :=
    (p : Π a : atom, (i1 a) <= (i2 a))

  instance : has_le I := ⟨I.less_than_or_equal⟩
  structure less_than (i1 : I) (i2 : I) : Prop :=
    (p : i1 <= i2) (q : ∃a : atom, (i1 a) < (i2 a))
  instance : has_lt I := ⟨I.less_than⟩ 
  lemma not_lt_exists {i1 i2 : I} (h : ¬i1 <= i2) : ∃ a : atom, (i2 a) < (i1 a) := begin
    by_contradiction exis,
    rw not_exists at exis,
    -- Not sure why I can't write simp as `rw not_lt at exis`
    -- not_lt relies on tv.linear_order so it's probably doing the conversion but not tracing it
    simp at exis,
    have le : i1 <= i2 := ⟨ exis ⟩,
    exact h le,
  end


  def sup (i1 i2 : I) : I := λ a, tv.sup (i1 a) (i2 a)
  def inf (i1 i2 : I) : I := λ a, tv.inf (i1 a) (i2 a)
  @[reducible] 
  noncomputable def Sup (S : set I) : I := λ a, tv.Sup (set.image (λ i : I, i a) S)
  @[reducible] 
  noncomputable def Inf (S : set I) : I := λ a, tv.Inf (set.image (λ i : I, i a) S)
  def top : I := λ a : atom, vtrue
  def bot : I := λ a : atom, vfalse

end I

namespace tv
  -- Logical conjunction of a list of truth values
  def conj (l : list tv) : tv := foldl tv.inf tv.vtrue l
  -- Logical disjunction of a list of truth values
  def disj (l : list tv) : tv := foldl tv.sup tv.vfalse l
  -- Logical complement of a list of truth values
  @[simp, reducible] def neg (v : tv) : tv := tv.cases_on v tv.vfalse tv.vundef tv.vtrue
  instance : has_neg tv := ⟨neg⟩ 
  def negl (l : list tv) : list tv := map tv.neg l
  lemma neg_antitone : antitone tv.neg := λ a b c, begin
    by_cases b.neg = a.neg, exact (eq.symm h).ge,
    cases a; cases b,
    any_goals {contradiction}, any_goals {exact c},
    any_goals {exact nat.lt_succ_iff.mp c}, any_goals {exact nat.pred_le_iff.mp c},
  end
  lemma foldl_remove_default (hd : tv) {tl : list tv} : foldl min ⊤ (hd::tl) = foldl min hd tl := by { simp }
  lemma foldl_min_extract {a : tv} {l : list tv} : foldl min a l = min a (foldl min ⊤ l) := begin
    cases l, simp,
    rw foldl_remove_default,
    unfold foldl, 
    exact foldl_assoc,
  end
end tv

namespace I
  def eval (self : I) (atoms : list atom) : list tv := map self atoms
  lemma unfold_eval (self : I) {a : atom} {tl : list atom} : (self.eval (a::tl)) = (self a) :: (self.eval tl) := begin unfold I.eval, simp, end
  def assign (self : I) (a : atom) (v : tv) : I := λ b, if a = b then v else self b
  def assign' (a : atom) (v : tv) : I -> I := λ i, i.assign a v
  lemma assign_eq_assign' {i : I} {a : atom} {v : tv} : (i.assign a v) = I.assign' a v i := rfl

  lemma assign_noop (self : I) (c : atom) : self = self.assign c (self c) := begin
    unfold I.assign, ext1, split_ifs,
    exact congr_arg self (eq.symm h),
    refl,
  end
  lemma assign_step {i1 i2 : I} {a : atom} {v1 v2 : tv} (i_le : i1 <= i2) (v_le : v1 <= v2) : (i1.assign a v1) <= (i2.assign a v2) := begin
    apply I.less_than_or_equal.mk, assume b,  
    unfold I.assign,
    split_ifs,
    exact v_le,
    exact i_le.p b,
  end
  def neg (self : I) : I := λ a, tv.neg (self a)
  instance has_neg : has_neg I := ⟨I.neg⟩
  @[simp] lemma neg_eval {self : I} {atoms : list atom} : (tv.negl (self.eval atoms)) = ((-self).eval atoms) := map_map tv.neg self atoms
  -- Need to move to a location that has access to I.complete_lattice, but I don't have a use for this yet anyways.
  -- lemma neg_antitone : antitone neg := λ a b c, I.less_than_or_equal.mk (λ atom, tv.neg_antitone (c.p atom))
end I



