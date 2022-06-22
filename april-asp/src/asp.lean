import order.hom.complete_lattice
import program
import order.fixed_points
import .complete_lattice.I
-- Shouldn't need anything from here anymore?
-- import .complete_lattice.PI
open tv
open order_hom



def xT_propagate (i_pos i_neg : I) : Program -> I
| [] := i_pos
| (r::p) := (i_pos.assign r.head (r.eval_body i_pos i_neg)) ⊔ (xT_propagate p)
def T_propagate (p : Program) (i_neg i_pos : I) : I := xT_propagate i_pos i_neg p


theorem T_monotone (p : Program) (i_neg : I) : monotone (T_propagate p i_neg) := λ a b c, begin
  induction p,
  exact c,
  refine sup_le_sup _ p_ih,
  refine I.assign_step c _,
  exact Rule.eval_body_monotone p_hd i_neg c,
end

def T (p : Program) (i_neg : I) : I →o I := ⟨T_propagate p i_neg, T_monotone p i_neg⟩


lemma T_increasing {p : Program} {i ii : I} : ii <= T p i ii := begin
  induction p, refl,
  exact le_sup_of_le_right p_ih,
end


@[simp] lemma  T_fp_le_eq_iff {p : Program} {i ii : I} : T p i ii <= ii ↔ T p i ii = ii := 
  (iff.intro (λ h, le_antisymm h T_increasing) (λ h, (eq.symm h).ge))

lemma T_fp_eq_unstep {p_tl : Program} {p_hd : Rule}  {i ii : I} (h : i = T (p_hd::p_tl) ii i) : i = T p_tl ii i  := 
  le_antisymm T_increasing (sup_le_iff.mp (le_antisymm_iff.mp h).right).right

lemma T_fp_rule_sat_iff {p : Program} {i ii : I} : i = T p ii i ↔ ∀ r ∈ p, Rule.reduct_satisfied r i ii := begin
  -- ==>
  split; assume h,
  induction p,
  by_contradiction, finish,
  assume r rmem,
  change r.eval_body i ii <= r.eval_head i,
  cases rmem, rw <- rmem at h,
  change i = (λ b, if r.head = b then (r.eval_body i ii) else i b) ⊔ (xT_propagate i ii p_tl) at h,  
  cases r.eval_body i ii,
  any_goals { rw h, unfold Rule.eval_head, refine le_sup_iff.mpr _, left, simp },
  exact p_ih (T_fp_eq_unstep h) r rmem,
  -- <==
  refine le_antisymm T_increasing _,
  induction p, 
  exact rfl.ge,
  change (i.assign p_hd.head (p_hd.eval_body i ii)) ⊔ (xT_propagate i ii p_tl) <= i,
  apply sup_le_iff.mpr,
  split,
  have h2 := @h p_hd (or.inl rfl), change p_hd.eval_body i ii <= p_hd.eval_head i at h2,
  unfold I.assign,
  refine I.less_than_or_equal.mk _, assume a,
  split_ifs,
  rw <- h_1, exact h2,
  exact rfl.le,
  refine p_ih _, simp at *, assume r rmem, exact h.right r rmem,
end

theorem T_fp_model_iff {p : Program} {i : I} : i = T p i i ↔ p.model i :=
  (iff.intro (λ h, ⟨ T_fp_rule_sat_iff.mp h ⟩)
             (λ h, T_fp_rule_sat_iff.mpr h.p))


def Program.is_local_op (p : Program) (f : I -> I) := ∀ {i : I}, p.localize (f i) = f (p.localize i)


def Program.is_local_biop (p : Program) (f : I -> I -> I) := ∀ {i1 i2 : I}, p.localize (f i1 i2) = f (p.localize i1) (p.localize i2)


lemma I.assign.is_local_op {p : Program} (v : tv) {a : atom} (amem : a ∈ p.atoms) : p.is_local_op (I.assign' a v) := begin
  assume i, unfold I.assign', unfold I.assign, ext,
  unfold Program.localize, simp, unfold localize, split_ifs, repeat{refl},
  rw h_1 at amem, contradiction, repeat{refl},
end

lemma I.sup_right.is_local_biop {p : Program} : p.is_local_biop I.sup := begin
  intros i1 i2, ext a, unfold I.sup, unfold Program.localize, simp, unfold localize, split_ifs, repeat{refl},
end

lemma I.eval.unlocalize {p : Program} {i : I} {atoms : list atom} : (∀ a ∈ atoms, a ∈ p.atoms) -> (p.localize i).eval atoms = i.eval atoms := begin
  intro all_atoms,
  induction atoms, refl,
  unfold I.eval, repeat {rw list.map_cons},
  have atoms_hd_pmem : atoms_hd ∈ p.atoms := all_atoms atoms_hd (list.mem_cons_self atoms_hd atoms_tl),
  have atoms_hd_unchanged : p.localize i atoms_hd = i atoms_hd := by {unfold Program.localize, simp, unfold localize, split_ifs, refl},
  rw atoms_hd_unchanged,
  have rest_eq : list.map ((p.localize) i) atoms_tl = list.map i atoms_tl := begin
    apply atoms_ih, intros b bmem, apply all_atoms, exact list.mem_of_mem_tail bmem,
  end,
  rw rest_eq,
end

lemma Rule.eval_pbody.unlocalize {p : Program} {r : Rule} (i : I) (pmem : r ∈ p) : r.eval_pbody (p.localize i) = r.eval_pbody i := by {
  unfold Rule.eval_pbody, rw I.eval.unlocalize (r.atom_program_mem_pbody pmem) }
lemma Rule.eval_nbody.unlocalize {p : Program} {r : Rule} (i : I) (pmem : r ∈ p) : r.eval_nbody (p.localize i) = r.eval_nbody i := by {
  unfold Rule.eval_nbody, rw I.eval.unlocalize (r.atom_program_mem_nbody pmem) }
lemma Rule.eval_body.unlocalize {p : Program} {r : Rule} (i ii : I) (pmem : r ∈ p) : r.eval_body (p.localize i) (p.localize ii) = r.eval_body i ii := by {
  unfold Rule.eval_body, rw [Rule.eval_pbody.unlocalize i pmem, Rule.eval_nbody.unlocalize ii pmem]}
lemma Rule.eval_body_pos.unlocalize {p : Program} {r : Rule} {i ii : I} (pmem : r ∈ p) : r.eval_body (p.localize i) ii = r.eval_body i ii := by {
  unfold Rule.eval_body, rw [Rule.eval_pbody.unlocalize i pmem]}


lemma T.is_local_op {p : Program} {ii : I} : p.is_local_op (T p ii) := λ i, begin
  have generalized : ∀ {p' : Program}, p ⊆ p' -> (p'.localize) ((T p ii) i) = (T p ii) ((p'.localize) i) := λ p' pss, begin
    unfold T, simp, unfold T_propagate, induction p, refl, unfold xT_propagate, unfold has_sup.sup,
    rw [I.sup_right.is_local_biop, I.assign_eq_assign', I.assign.is_local_op, <-I.assign_eq_assign'],
    have p_hd_mem_p' : p_hd ∈ p' := pss (list.mem_cons_self p_hd p_tl),
    rw [Rule.eval_body_pos.unlocalize p_hd_mem_p'],
    refine sup_eq_sup_split (and.intro rfl _), simp,
    exact p_ih (list.cons_subset.mp pss).right,
    exact Exists.intro p_hd (Exists.intro ((list.cons_subset.mp pss).left) (or.inl rfl)),
  end,
  exact generalized rfl.subset,
end

@[reducible]
def T_repeat (p : Program) (i_neg : I) : Π(i_pos : I), I
| i := (T p i_neg) i

def T_lfp (p : Program) (i_neg : I) := T_repeat p i_neg I.bot

lemma fuck (p : Program) (i_neg : I) : lfp (T p i_neg) = T_lfp p i_neg := sorry

theorem T_fp_stable_model_iff {p : Program} {i : I}: i = lfp (T p i) ↔ p.stable_model i := begin
split; assume h,
unfold lfp at h, simp at h,
change i = Inf {a : I | (T p i) a = a} at h,
have i_fp : (T p i) i = i := begin
  -- suggest,
end,
refine Program.stable_model.mk (T_fp_model_iff.mp h) _,
sorry,

end