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

  def le (i1 i2 : I) := I.less_than_or_equal i1 i2
  def lt (i1 i2 : I) := I.less_than i1 i2
  @[refl] lemma le_refl (i : I) : i <= i := ⟨λ a, le_refl (i a)⟩ 
  @[trans] lemma le_trans {a b c : I} (h1 : a ≤ b) : b ≤ c → a ≤ c := λ h2, ⟨λ a, le_trans (h1.p a) (h2.p a)⟩
  lemma le_antisymm {n m : I} (h1 : n <= m) : m <= n -> n = m := λ h2, funext (λ a : atom, le_antisymm (h1.p a) (h2.p a))
  lemma lt_iff_le_not_le {a b : I} : a < b ↔ (a ≤ b ∧ ¬ b ≤ a) := iff.intro
    (λ l, begin
      split, exact l.p,
      by_contradiction p,
      cases l.q with w kk,
      exact ((lt_iff_le_not_le.mp kk).right) (p.p w) end)
    (λ r, begin
      split, exact r.left,
      exact I.not_lt_exists r.right,
    end)
  instance partial_order : partial_order I :=
  { le := le,
    lt := lt,
    le_refl := le_refl,
    le_trans := @le_trans,
    le_antisymm := @le_antisymm,
    lt_iff_le_not_le := @lt_iff_le_not_le }

  def top (a : atom) : tv := vtrue
  lemma le_top (i : I) : i <= I.top := I.less_than_or_equal.mk (λ a : atom, tv.le_top (i a))
  def bot (a : atom) : tv := vfalse
  lemma bot_le (i : I) : I.less_than_or_equal I.bot i := I.less_than_or_equal.mk (λ a, tv.bot_le (i a))

  instance bounded_order : bounded_order I := {
    top := I.top,
    le_top := I.le_top,
    bot := I.bot,
    bot_le := I.bot_le,
  }

  def sup (i1 i2 : I) : I := λ a, tv.sup (i1 a) (i2 a)
  instance has_sup : has_sup I := ⟨I.sup⟩
  @[simp] lemma sup_le (a b c : I) : a <= c -> b <= c -> a ⊔ b <= c := (λ h g, ⟨(λ x, max_le (h.p x) (g.p x))⟩)
  @[simp] lemma le_sup_right (a b : I) : b <= a ⊔ b := ⟨λ x, le_max_right (a x) (b x)⟩
  @[simp] lemma le_sup_left (a b : I) : a <= a ⊔ b  := ⟨λ x, le_max_left (a x) (b x)⟩

  def inf (i1 i2 : I) : I := λ a, tv.inf (i1 a) (i2 a)
  instance has_inf : has_inf I := ⟨I.inf⟩
  @[simp] lemma le_inf (a b c : I) : a <= b -> a <= c -> a <= b ⊓ c := (λ h g, ⟨(λ x, le_min (h.p x) (g.p x))⟩)
  @[simp] lemma inf_le_right (a b : I) : a ⊓ b <= b:= ⟨λ x, min_le_right (a x) (b x)⟩
  @[simp] lemma inf_le_left (a b : I) : a ⊓ b <= a  := ⟨λ x, min_le_left (a x) (b x)⟩

  @[reducible] 
  noncomputable def Sup (S : set I) : I := λ a, tv.Sup (set.image (λ i : I, i a) S)
  @[reducible] 
  noncomputable instance has_Sup : has_Sup I := ⟨I.Sup⟩
  @[reducible]
  noncomputable def Inf (S : set I) : I := λ a, tv.Inf (set.image (λ i : I, i a) S)
  @[reducible] 
  noncomputable instance has_Inf : has_Inf I := ⟨I.Inf⟩



  lemma le_Sup (S : set I) (i : I) (m : i ∈ S) : i <= (I.Sup S) := ⟨ λ a, begin
  let imager := (λ i : I, i a),
  let mapped_set := set.image imager S,
  have tv_le_Sup := tv.complete_lattice.le_Sup,
  have y := tv_le_Sup mapped_set (i a),
  have z : (i a) ∈ mapped_set := set.mem_image_of_mem imager m,
  exact y z,
  end⟩

  lemma Sup_le (S : set I) (i : I) (p : ∀ o ∈ S, o <= i) : (I.Sup S) <= i := ⟨ λ a, begin
  let imager := (λ i : I, i a),
  let mapped_set := set.image imager S,
  have tv_Sup_le := tv.complete_lattice.Sup_le,
  have y := tv_Sup_le mapped_set (i a),
  simp at y,
  exact y (λ j k, ((p j) k).p a),
  end⟩

  -- Proof is near identical to le_Sup
  lemma Inf_le (S : set I) (i : I) (m : i ∈ S) : (I.Inf S) <= i := ⟨ λ a, begin
  let imager := (λ i : I, i a),
  let mapped_set := set.image imager S,
  have tv_le_Sup := tv.complete_lattice.Inf_le,
  have y := tv_le_Sup mapped_set (i a),
  have z : (i a) ∈ mapped_set := set.mem_image_of_mem imager m,
  exact y z,
  end⟩

  -- Proof is near identical to Sup_le
  lemma le_Inf (S : set I) (i : I) (p : ∀ o ∈ S, i <= o) : i <= (I.Inf S) := ⟨ λ a, begin 
  let imager := (λ i : I, i a),
  let mapped_set := set.image imager S,
  have tv_Sup_le := tv.complete_lattice.le_Inf,
  have y := tv_Sup_le mapped_set (i a),
  simp at y,
  exact y (λ j k, ((p j) k).p a),
  end⟩

  @[reducible] noncomputable instance complete_lattice : complete_lattice I := {
    le := I.le,
    sup := I.sup,
    sup_le := I.sup_le,
    le_sup_right := I.le_sup_right,
    le_sup_left := I.le_sup_left,
    inf := I.inf,
    le_inf := I.le_inf,
    inf_le_right := I.inf_le_right,
    inf_le_left := I.inf_le_left,
    Sup := I.Sup,
    le_Sup := I.le_Sup,
    Sup_le := I.Sup_le,
    Inf := I.Inf,
    le_Inf := I.le_Inf,
    Inf_le := I.Inf_le,
    ..I.partial_order,
    ..I.bounded_order,
  }
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
  lemma neg_antitone : antitone neg := λ a b c, I.less_than_or_equal.mk (λ atom, tv.neg_antitone (c.p atom))
end I



