import ..primitives
import ..program
import ..misc
open tv
open order_hom
open atom


def Program.I.sup {p : Program} (a b : p.I) : p.I := p.localize $ I.sup a b
instance {p : Program} : has_sup p.I := ⟨@Program.I.sup p⟩
def Program.I.inf {p : Program} (a b : p.I) : p.I := p.localize $ I.inf a b
instance {p : Program} : has_inf p.I := ⟨@Program.I.inf p⟩
def Program.I.bot {p : Program} := p.localize I.bot
instance {p : Program} : has_bot p.I := ⟨@Program.I.bot p⟩
def Program.I.top {p : Program} := p.localize I.top
instance {p : Program} : has_top p.I := ⟨@Program.I.top p⟩
instance Program.I.partial_order {p : Program} : partial_order p.I := partial_order.lift (@Program.I.i p) (@Program.I.i.inj p)

def Program.I.less_than_or_equal (p : Program) := (@Program.I.partial_order p).le


lemma Program.I.bot_eq_I_bot {p : Program} : (@Program.I.bot p).i = I.bot := by {ext, unfold Program.I.i, split_ifs; refl}

lemma Program.I.le_top {p : Program} (pi : p.I) : pi <= ⊤ := begin
  change pi.i <= Program.I.top.i,
  apply I.less_than_or_equal.mk, assume a,
  unfold Program.I.i, split_ifs,
  exact le_top, exact rfl.le,
end
lemma Program.I.bot_le {p : Program} (pi : p.I) : ⊥ <= pi := begin
  change Program.I.bot.i <= pi,
  rw Program.I.bot_eq_I_bot,
  exact bot_le,
end

instance Program.I.bounded_order {p : Program} : bounded_order p.I := {
  top := Program.I.top,
  le_top := Program.I.le_top,
  bot := Program.I.bot,
  bot_le := Program.I.bot_le,
}


@[simp] lemma Program.I.sup_distrib {p : Program} (a b : p.I) : (a ⊔ b).i = a.i ⊔ b.i := begin
  ext, change (a ⊔ b).i x = (a.i ⊔ b.i) x,
  change dite (x ∈ p.atoms) (λ (c : x ∈ p.atoms), (a ⊔ b).e x c) (λ (a : x ∉ p.atoms), vfalse) = (a.i ⊔ b.i) x,
  split_ifs,
  change (p.localize $ I.sup a.i b.i).e x h = (a.i ⊔ b.i) x,
  unfold Program.localize, simp, refl,
  change vfalse = if (b.i x) <= (a.i x) then (a.i x) else (b.i x),
  split_ifs,
  all_goals { unfold Program.I.i; finish },
end

@[simp] lemma Program.I.inf_distrib {p : Program} (a b : p.I) : (a ⊓ b).i = a.i ⊓ b.i := begin
  ext, change (a ⊓ b).i x = (a.i ⊓ b.i) x,
  change dite (x ∈ p.atoms) (λ (c : x ∈ p.atoms), (a ⊓ b).e x c) (λ (a : x ∉ p.atoms), vfalse) = (a.i ⊓ b.i) x,
  split_ifs,
  change (p.localize $ I.inf a.i b.i).e x h = (a.i ⊓ b.i) x,
  unfold Program.localize, simp, refl,
  change vfalse = min (a.i x) (b.i x),
  change vfalse = if (a.i x) <= (b.i x) then (a.i x) else (b.i x),
  split_ifs,
  all_goals { unfold Program.I.i; finish },
end

-- These wrapper proofs are longer than the original proofs :(
@[simp] lemma Program.I.sup_le {p : Program} (a b c : p.I) : a <= c -> b <= c -> a ⊔ b <= c := begin
  change a.i ≤ c.i → b.i ≤ c.i → (p.localize (a.i ⊔ b.i)).i ≤ c.i,
  rw [<-Program.I.sup_distrib, Program.I_eq_PI, Program.I.sup_distrib],
  exact I.sup_le a b c,
end
@[simp] lemma Program.I.le_sup_right {p : Program} (a b : p.I) : b <= a ⊔ b := begin
  change b.i <= (p.localize (a.i ⊔ b.i)).i,
  rw [<-Program.I.sup_distrib, Program.I_eq_PI, Program.I.sup_distrib],
  exact I.le_sup_right a b,
end
@[simp] lemma Program.I.le_sup_left {p : Program} (a b : p.I) : a <= a ⊔ b := begin
  change a.i <= (p.localize (a.i ⊔ b.i)).i,
  rw [<-Program.I.sup_distrib, Program.I_eq_PI, Program.I.sup_distrib],
  exact I.le_sup_left a b,
end
@[simp] lemma Program.I.le_inf {p : Program} (a b c : p.I) : a <= b -> a <= c -> a <= b ⊓ c := begin
  change a.i ≤ b.i → a.i ≤ c.i → a.i <= (p.localize (b.i ⊓ c.i)).i,
  rw [<-Program.I.inf_distrib, Program.I_eq_PI, Program.I.inf_distrib],
  exact I.le_inf a b c,
end
@[simp] lemma Program.I.inf_le_right {p : Program} (a b : p.I) : a ⊓ b <= b:= begin
  change (p.localize (a.i ⊓ b.i)).i <= b.i,
  rw [<-Program.I.inf_distrib, Program.I_eq_PI, Program.I.inf_distrib],
  exact I.inf_le_right a b,
end
@[simp] lemma Program.I.inf_le_left {p : Program} (a b : p.I) : a ⊓ b <= a := begin
  change (p.localize (a.i ⊓ b.i)).i <= a.i,
  rw [<-Program.I.inf_distrib, Program.I_eq_PI, Program.I.inf_distrib],
  exact I.inf_le_left a b,
end

@[reducible] 
noncomputable def Program.I.Sup {p : Program} (S : set p.I) : p.I := p.localize $ I.Sup S
@[reducible] 
noncomputable instance Program.I.has_Sup {p : Program} : has_Sup p.I := ⟨@Program.I.Sup p⟩
@[reducible]
noncomputable def Program.I.Inf {p : Program} (S : set p.I) : p.I := p.localize $ I.Inf S
@[reducible] 
noncomputable instance Program.I.has_Inf {p : Program} : has_Inf p.I := ⟨@Program.I.Inf p⟩


@[simp] lemma Program.I.Sup_distrib {p : Program} (S : set p.I) : (Program.I.Sup S).i = I.Sup (Program.I.i '' S) := begin
  ext, change dite (x ∈ p.atoms) (λ (c : x ∈ p.atoms), (Program.I.Sup S).e x c) (λ (a : x ∉ p.atoms), vfalse) = I.Sup (Program.I.i '' S) x,
  split_ifs, refl,
  change vfalse = tv.Sup ((λ (i : I), i x) '' (Program.I.i '' S)),
  symmetry, apply Sup_eq_bot.mpr, assume a b,
  simp at b, cases b with z x, rw <-x.right, unfold Program.I.i, simp, split_ifs, refl,
end

-- Unlike Program.I.Sup_distrib, this only works when S is nonempty
@[simp] lemma Program.I.Inf_distrib {p : Program} {S : set p.I} (Snm : S.nonempty) : (Program.I.Inf S).i = I.Inf (Program.I.i '' S) := begin
  ext, change dite (x ∈ p.atoms) (λ (c : x ∈ p.atoms), (Program.I.Inf S).e x c) (λ (a : x ∉ p.atoms), vfalse) = I.Inf (Program.I.i '' S) x,
  split_ifs, refl,
  change vfalse = tv.Inf ((λ (i : I), i x) '' (Program.I.i '' S)),
  symmetry, apply Inf_eq_bot.mpr, assume a b,
  simp at b, refine Exists.intro ⊥ (Exists.intro _ _), work_on_goal 2 { exact b,},
  simp, cases Snm with y1 y2, refine Exists.intro y1 (and.intro y2 _),
  unfold Program.I.i, simp, finish,
end

@[simp] lemma Program.I.I_upcast {p : Program} {o : I} {pi : p.I} : o = pi.i  -> (p.localize o).i = o := begin
  assume h, ext, unfold Program.I.i at |- h, have hh := function.funext_iff.mp h x, split_ifs at |- hh,
  refl, symmetry, exact hh,
end

lemma Program.I.I_mem_upcast_exists {p : Program} {o : I} {S : set p.I} (omem : o ∈ (Program.I.i '' S)) : ∃ pi : p.I, o = pi.i := begin
  rw set.mem_image at omem, cases omem with pi b,
  exact Exists.intro pi b.right.symm,
end

 lemma Program.I.I_mem_upcast {p : Program} {o : I} {S : set p.I} (omem : o ∈ (Program.I.i '' S)) : (p.localize o) ∈ S := begin
  rw set.mem_image at omem, cases omem with pi b,
  rw [<-b.right, Program.I_eq_PI], exact b.left,
end

lemma Program.I.le_Sup {p : Program} (S : set p.I) (i : p.I) (m : i ∈ S) : i <= (Program.I.Sup S) := begin
  change i.i <= (p.localize $ I.Sup (Program.I.i '' S)).i,
  rw [<-Program.I.Sup_distrib, Program.I_eq_PI, Program.I.Sup_distrib],
  exact I.le_Sup S i (set.mem_image_of_mem (Program.I.i) m),
end

lemma Program.I.Sup_le {p : Program} (S : set p.I) (i : p.I) (pp : ∀ o ∈ S, o <= i) : (Program.I.Sup S) <= i := begin
  have h := I.Sup_le S i (λ o omem, begin
    have gg := pp (p.localize o) (Program.I.I_mem_upcast omem),
    have j : (p.localize o).i = o := begin 
      have y := Program.I.I_mem_upcast_exists omem,
      cases y with p p2,
      exact Program.I.I_upcast p2,
    end,
    rw <-j, exact gg,
  end),
  change (p.localize $ I.Sup (Program.I.i '' S)).i <= i.i,
  rw [<-Program.I.Sup_distrib, Program.I_eq_PI, Program.I.Sup_distrib],
  exact h,
end

lemma Program.I.Inf_le {p : Program} (S : set p.I) (i : p.I) (m : i ∈ S) : (Program.I.Inf S) <= i := begin
  change (p.localize $ I.Inf (Program.I.i '' S)).i <= i.i,
  have distrib := Program.I.Inf_distrib (Exists.intro i m),
  rw [<-distrib, Program.I_eq_PI, distrib],
  exact I.Inf_le S i (set.mem_image_of_mem (Program.I.i) m),
end

lemma Program.I.non_mem_eval {p : Program} {pi : p.I} {x : atom} (xnmem : x ∉ p.atoms) : pi x = ⊥ := by { unfold_coes, unfold Program.I.i, split_ifs, refl }

lemma Program.I.set_non_mem_eval {p : Program} {S : set p.I} {x : atom} (Snm : S.nonempty) (xnmem : x ∉ p.atoms) : (λ (i : I), i x) '' (Program.I.i '' S) = { ⊥ } := begin
  ext, split; assume h,
  all_goals {simp at |- h, cases h with pi h2},
  rw <-h2.right, exact Program.I.non_mem_eval xnmem,
  cases Snm with pi p, exact Exists.intro pi (and.intro p (Program.I.non_mem_eval xnmem)),
end

-- lemma Program.I.Inf_insert_top_outside { p : Program } {S : set p.I} : p.localize (I.Inf (Program.I.i '' S)) = p.localize (I.Inf (insert (@Program.I.top p) (Program.I.i '' S))) := begin
--   unfold Program.localize, simp,
--   ext a a_mem,
--   unfold_coes,
--   change I.Inf (Program.I.i '' S) a = (I.Inf (insert Program.I.top.i (Program.I.i '' S))) a,
--   have f := @Inf_insert I _ Program.I.top.i  (Program.I.i '' S),
--   change I.Inf (insert Program.I.top.i (Program.I.i '' S)) = Program.I.top.i ⊓ Inf (Program.I.i '' S) at f,
--   rw f,
--   apply le_antisymm,
--   apply le_inf,
--   have le_top := le_top
-- end

-- #check Inf_insert

-- lemma Program.I.Inf_insert {p : Program} {S : set p.I} : p.localize (I.Inf (Program.I.i '' S)) = p.localize (I.Inf (Program.I.i '' (insert ⊤ S))) := begin
--   have top_outside : p.localize (I.Inf (Program.I.i '' S)) = p.localize (I.Inf (insert Program.I.top (Program.I.i '' S))) := Program.I.Inf_insert_top_outside,
--   rw top_outside,
--   ext, unfold I.Inf,
--   have wo_Inf : (λ (i : I), i x) '' insert (@Program.I.top p) (Program.I.i '' S) = (λ (i : I), i x) '' (Program.I.i '' (insert ⊤ S)) := begin
--     ext, unfold_coes, simp, split; assume h,
--     cases h with x2, 
--     have x_pi := p.localize x2,
--     cases h_h, cases h_h_left,
--     have l : p.localize x2 = ⊤ := begin
--       rw [h_h_left, Program.I_eq_PI], refl,
--     end,
--     refine Exists.intro (p.localize x2) _,
--     refine (and.intro (or.inl l) _),
--     rw [<-h_h_right, h_h_left, <-h_h_left, l, h_h_left], refl,
--     cases h_h_left with pi foo,
--     refine Exists.intro pi (and.intro (or.inr foo.left) _),
--     rw [foo.right, h_h_right],
--     cases h with pi cond,
--     cases cond, cases cond_left,
--     refine Exists.intro pi.i _, split, left,
--     rw cond_left, refl,
--     exact cond_right,
--     refine Exists.intro pi.i (and.intro (or.inr _) _),
--     exact Exists.intro pi (and.intro cond_left rfl),
--     exact cond_right,
--   end,
--   unfold Program.localize, simp,
--   rw wo_Inf,
-- end

lemma Program.I.le_upcast {p : Program} {pi : p.I} {i : I} : pi.i <= i -> pi.i <= (p.localize i).i := λ h, begin
  fconstructor, assume a,
  have hh := h.p a, unfold Program.localize, unfold Program.I.i at |- hh,
  split_ifs at |- hh,
  exact hh, exact rfl.le,
end


lemma Program.I.le_Inf {p : Program} (S : set p.I) (i : p.I) (pp : ∀ o ∈ S, i <= o) : i <= Inf S := begin
  have h := I.le_Inf S i (λ o omem, begin
    have gg := pp (p.localize o) (Program.I.I_mem_upcast omem),
    have j : (p.localize o).i = o := begin 
      have y := Program.I.I_mem_upcast_exists omem,
      cases y with p p2,
      exact Program.I.I_upcast p2,
    end,
    rw <-j, exact gg,
  end),
  exact Program.I.le_upcast h,
end


  @[reducible] noncomputable instance Program.I.complete_lattice {p : Program} : complete_lattice p.I := {
    sup := Program.I.sup,
    sup_le := Program.I.sup_le,
    le_sup_right := Program.I.le_sup_right,
    le_sup_left := Program.I.le_sup_left,
    inf := Program.I.inf,
    le_inf := Program.I.le_inf,
    inf_le_right := Program.I.inf_le_right,
    inf_le_left := Program.I.inf_le_left,
    Sup := Program.I.Sup,
    le_Sup := Program.I.le_Sup,
    Sup_le := Program.I.Sup_le,
    Inf := Program.I.Inf,
    le_Inf := Program.I.le_Inf,
    Inf_le := Program.I.Inf_le,
    ..Program.I.partial_order,
    ..Program.I.bounded_order,
  }
