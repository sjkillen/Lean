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


def Program.is_local_op (p : Program) (f : I -> I) := ∀ {i : I}, p.localize (f i) = f (p.localize i)
def Program.is_local_biop (p : Program) (f : I -> I -> I) := ∀ {i1 i2 : I}, p.localize (f i1 i2) = f (p.localize i1) (p.localize i2)


lemma I.assign'.is_local_op {p : Program} (v : tv) {a : atom} (amem : a ∈ p.atoms) : p.is_local_op (I.assign' a v) := begin
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

-- lemma tv.conj.unlocalize {p : Program} {i : I} {atoms : list atom} : (∀ a ∈ atoms, a ∈ p.atoms) -> tv.conj 

lemma Rule.eval_pbody.unlocalize {p : Program} {r : Rule} (i : I) (pmem : r ∈ p) : r.eval_pbody (p.localize i) = r.eval_pbody i := by {
  unfold Rule.eval_pbody, rw I.eval.unlocalize (r.atom_program_mem_pbody pmem) }
lemma Rule.eval_nbody.unlocalize {p : Program} {r : Rule} (i : I) (pmem : r ∈ p) : r.eval_nbody (p.localize i) = r.eval_nbody i := by {
  unfold Rule.eval_nbody, rw I.eval.unlocalize (r.atom_program_mem_nbody pmem) }
lemma Rule.eval_body.unlocalize {p : Program} {r : Rule} (i ii : I) (pmem : r ∈ p) : r.eval_body (p.localize i) (p.localize ii) = r.eval_body i ii := by {
  unfold Rule.eval_body, rw [Rule.eval_pbody.unlocalize i pmem, Rule.eval_nbody.unlocalize ii pmem]}
lemma Rule.eval_body_pos.unlocalize {p : Program} {r : Rule} (i ii : I) (pmem : r ∈ p) : r.eval_body (p.localize i) ii = r.eval_body i ii := by {
  unfold Rule.eval_body, rw [Rule.eval_pbody.unlocalize i pmem]}



lemma T.is_local_op {p : Program} {ii : I} : p.is_local_op (T p ii) := begin
  change ∀ a, (p.localize) ((T p ii) a) = (T p ii) ((p.localize) a),
  have general_goal : ∀ (p2 : Program), p ⊆ p2 -> (∀ a, (p2.localize) ((T p ii) a) = (T p ii) ((p2.localize) a)) := begin
    assume p2,
    unfold T, simp, unfold T_propagate, induction p,
    intros nsub x, refl,
    unfold xT_propagate,
    intros nsub a,
    change (Program.localize p2) (I.sup (a.assign p_hd.head (p_hd.eval_body a ii)) (xT_propagate a ii p_tl)) =
    ((Program.localize p2) a).assign p_hd.head
        (p_hd.eval_body ((Program.localize p2) a) ii) ⊔
      xT_propagate ((Program.localize p2) a) ii p_tl,
    rw [I.sup_right.is_local_biop, I.assign_eq_assign', I.assign'.is_local_op],
    have y : (Program.localize p2) (xT_propagate a ii (p_tl)) = xT_propagate ((Program.localize p2) a) ii (p_tl) := begin
      sorry,
    end,
    rw y,
    (I.assign' p_hd.head (p_hd.eval_body a ii) ((Program.localize (p_hd :: p_tl)) a)).sup (xT_propagate ((Program.localize (p_hd :: p_tl)) a) ii p_tl) =
    (((Program.localize (p_hd :: p_tl)) a).assign p_hd.head (p_hd.eval_body ((Program.localize (p_hd :: p_tl)) a) ii)).sup (xT_propagate ((Program.localize (p_hd :: p_tl)) a) ii p_tl),
    rw <-I.assign_eq_assign', rw Rule.eval_body_pos.unlocalize,
    exact list.mem_cons_self p_hd p_tl,
    refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _), left, refl,
  end
end


lemma fuck (a b c d : I) : a = c ∧ b = d -> a ⊓ b = c ⊓ d := begin
assume a, 
end

-- lemma T_fixpoint_ruleheads_iff {p : Program} {ii : I} {i : I} : i = (T p ii) i ↔ ∀ (r : Rule), r ∈ p → (T p ii) i r.head ≤ i r.head := begin
--   split; intro h, rw <-h, intros _ _, exact rfl.le,
--   refine le_antisymm T_increasing _, fconstructor,
--   assume a,
--   induction p, exact rfl.le,
  
--   -- unfold T, simp, unfold T_propagate, unfold xT_propagate,
--   -- apply sup_le,

-- end


-- @[reducible] lemma T_growth_witness {p : Program} {ii : I} (i : I) : i < (T p ii) i -> ∃ (r : Rule) (rmem : r ∈ p), (i r.head) < ((T p ii) i) r.head := begin
--   by_contradiction, simp at h,
--   exact (eq_iff_le_not_lt.mp (T_fixpoint_ruleheads_iff.mpr h.right)).right h.left,
-- end




-- TODO lost in this definition is that the atom that witnesses  i < i is in face r.head
-- Probably just need to decompose < unfornatunately
-- lemma attribute_rule_to_growth (p : Program) (i_pos i_neg : I)
--   : i_pos < (T_propagate p i_neg) i_pos -> ∃ (r : Rule) (rmem : r ∈ p), (i_pos r.head) < (T_propagate p i_neg) i_pos r.head := sorry


-- lemma T_PI_propagate.p_restricted {p : Program} {i_neg i_pos : p.I} 
--   : ∀ (a : atom), a ∉ p.atoms → i_pos a = T_propagate p i_neg.i i_pos a := begin
--     intros a cond,
--     contrapose cond,
--     simp,
--     have cond2 := ne.lt_or_lt cond,
--     cases cond2,
--     have j : i_pos.i <= T_propagate p i_neg.i i_pos.i := begin
--         -- Use monotone property
--         sorry
--     end,
--     have jh2 : i_pos.i < T_propagate p i_neg.i i_pos.i := ⟨j, Exists.intro a cond2⟩,
--     have u := attribute_rule_to_growth p i_pos i_neg jh2,
--     unfold_coes at u, unfold_coes at cond2,

--     -- have g : 
--     -- have h I.less_than_or_equal
--     -- have uu := u cond2,
--   --   unfold T_propagate, unfold xT_propagate,
--   --   apply le_antisymm,
--   --   apply le_sup_iff.mpr,

-- end

-- def T_PI_propagate {p : Program} (i_neg i_pos : p.I) : p.I := p.localize $ T_propagate p i_neg i_pos
-- lemma T_propagate_eq_PI {p : Program} {i_neg i_pos : p.I} : T_propagate p i_neg.i i_pos.i = T_PI_propagate i_neg i_pos := 
--   p_restricted (T_propagate p i_neg.i) i_pos T_PI_propagate.p_restricted

-- lemma T_PI_propagate.monotone {p : Program} (i_neg : p.I) : monotone (T_PI_propagate i_neg) := λ _ _ c, begin
--   have z := T_monotone p i_neg c,
-- end
-- def T_PI {p : Program} (i_neg : p.I) : p.I →o p.I := ⟨
--   (λ a, begin
--     have h := (@T_PI_propagate p i_neg) a,
    
--   end)
  
--   , T_PI_propagate.monotone i_neg⟩

-- -- lemma fuck {p : Program} {i ii : I} (k : i = Inf {a : I | (T p ii) a ≤ a}) : (T p ii) i = i := begin
-- --   refine funext _, assume a,

-- -- end



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