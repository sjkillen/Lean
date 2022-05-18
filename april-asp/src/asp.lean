import order.hom.complete_lattice
import program
import order.fixed_points
import .complete_lattice.I
import .complete_lattice.PI
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


def p_restricted {p : Program} (f : I -> I) (i : p.I) (u : ∀a ∉ p.atoms, i a = (f i) a) : f i = p.localize (f i) := begin
  ext,
  by_cases x ∉ p.atoms,
  have uu := u x h,
  rw <-uu,
  unfold Program.localize,
  unfold_coes, unfold Program.I.i,
  simp,
  split_ifs, refl,
  simp at h,
  unfold Program.localize,
  change f ⇑i x = ((@Program.I.mk p (λ (a : atom) (amem : a ∈ p.atoms), f ⇑i a)).i x),
  unfold Program.I.i, split_ifs, refl,
end

-- TODO lost in this definition is that the atom that witnesses  i < i is in face r.head
-- Probably just need to decompose < unfornatunately
lemma attribute_rule_to_growth (p : Program) (i_pos i_neg : I)
  : i_pos < (T_propagate p i_neg) i_pos -> ∃ (r : Rule) (rmem : r ∈ p), (i_pos r.head) < (T_propagate p i_neg) i_pos r.head := sorry


lemma T_PI_propagate.p_restricted {p : Program} {i_neg i_pos : p.I} 
  : ∀ (a : atom), a ∉ p.atoms → i_pos a = T_propagate p i_neg.i i_pos a := begin
    intros a cond,
    contrapose cond,
    simp,
    have cond2 := ne.lt_or_lt cond,
    cases cond2,
    have j : i_pos.i <= T_propagate p i_neg.i i_pos.i := begin
        -- Use monotone property
        sorry
    end,
    have jh2 : i_pos.i < T_propagate p i_neg.i i_pos.i := ⟨j, Exists.intro a cond2⟩,
    have u := attribute_rule_to_growth p i_pos i_neg jh2,
    unfold_coes at u, unfold_coes at cond2,

    -- have g : 
    -- have h I.less_than_or_equal
    -- have uu := u cond2,
  --   unfold T_propagate, unfold xT_propagate,
  --   apply le_antisymm,
  --   apply le_sup_iff.mpr,

end
#check ne.lt_or_lt

-- lemma search {α : Type} [complete_linear_order α] (a b : α) : ¬(a = b) -> a < b ∨ b < a := begin
--   exact ne.lt_or_lt,
-- end

def T_PI_propagate {p : Program} (i_neg i_pos : p.I) : p.I := p.localize $ T_propagate p i_neg i_pos
lemma T_propagate_eq_PI {p : Program} {i_neg i_pos : p.I} : T_propagate p i_neg.i i_pos.i = T_PI_propagate i_neg i_pos := 
  p_restricted (T_propagate p i_neg.i) i_pos T_PI_propagate.p_restricted

lemma T_PI_propagate.monotone {p : Program} (i_neg : p.I) : monotone (T_PI_propagate i_neg) := λ _ _ c, begin
  have z := T_monotone p i_neg c,
end
def T_PI {p : Program} (i_neg : p.I) : p.I →o p.I := ⟨
  (λ a, begin
    have h := (@T_PI_propagate p i_neg) a,
    
  end)
  
  , T_PI_propagate.monotone i_neg⟩

-- lemma fuck {p : Program} {i ii : I} (k : i = Inf {a : I | (T p ii) a ≤ a}) : (T p ii) i = i := begin
--   refine funext _, assume a,

-- end



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