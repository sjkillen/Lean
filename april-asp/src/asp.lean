import order.hom.complete_lattice
import program
import order.fixed_points
open tv
open order_hom

#check order_hom.lfp


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





lemma fuck {p : Program} {i ii : I} (k : i = Inf {a : I | (T p ii) a ≤ a}) : (T p ii) i = i := begin
  refine funext _, assume a,

end

#check lfp


theorem T_fp_stable_model_iff {p : Program} {i : I}: i = lfp (T p i) ↔ p.stable_model i := begin
split; assume h,
unfold lfp at h, simp at h,
change i = Inf {a : I | (T p i) a = a} at h,
have i_fp : (T p i) i = i := begin
  -- suggest,
end,
refine Program.stable_model.mk (T_fp_model_iff.mp h) _,
sorry,

-- all_goals { assume h },
-- unfold_coes, unfold lfp, simp, unfold_coes, unfold T, simp,
-- by_contradiction u,
-- let jj := i ⊓ Inf {a : I | T_propagate p i a ≤ a},
-- let j : jj < i := sorry,
-- have pp := h.p jj j,



-- exact sorry,
-- -- simp,
-- refine Inf_le_of_le _ _,
-- assume b bm,

-- exact sorry,
-- exact Inf_le (T_model_fp' model),

-- -- by_contradiction q, simp at q,
-- -- simp at q,
-- exact sorry,
-- -- Eliminate the Inf :)
-- -- simp,
-- assume b tp,


-- exact sorry,
-- fconstructor, assumption,
-- assume ii ii_lt_i,
-- by_contradiction,
-- have u := h.p,
-- have uy := model.p,
-- sorry
end