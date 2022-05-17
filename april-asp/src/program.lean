/-
Defines a normal ASP program and its three-valued semantics
-/

import primitives
import misc
open tv
open order_hom
open atom

structure Rule :=
  (head : atom)
  (pbody : list atom)
  (nbody : list atom)
def Program := list Rule


-- set_option trace.simplify.rewrite true


namespace Rule
  def eval_pbody (self : Rule) (i : I) : tv := tv.conj (i.eval self.pbody) 
  def eval_nbody (self : Rule) (i : I) : tv := tv.conj (tv.negl (i.eval self.nbody))
  def eval_body (self : Rule) (i_pos i_neg : I) : tv := (self.eval_pbody i_pos) ⊓ (self.eval_nbody i_neg)
  def eval_head (self : Rule) (i : I) : tv := i self.head

  @[simp] def eval_pbody_monotone (r : Rule) : monotone r.eval_pbody := λ a b c, begin
    unfold Rule.eval_pbody,
    induction r.pbody, exact rfl.ge,
    unfold tv.conj at |- ih, unfold tv.inf at |- ih,
    rw [I.unfold_eval a, I.unfold_eval b],
    have t : ⊤ = vtrue := by { refl },
    have rd_a := tv.foldl_remove_default (a hd),
    have rd_b := tv.foldl_remove_default (b hd),
    rw t at rd_a rd_b, rw [rd_a, rd_b], rw [@tv.foldl_min_extract (a hd), @tv.foldl_min_extract (b hd)],
    exact min_le_min (c.p hd) ih,
  end

  def eval_body_monotone (r : Rule) (i_neg : I) : monotone (λ i_pos, r.eval_body i_pos i_neg) :=
      λ a b c, inf_le_inf (eval_pbody_monotone r c) (rfl.ge)

  def reduct_satisfied (r : Rule) (i_pos i_neg : I) : Prop := r.eval_body i_pos i_neg <= r.eval_head i_pos
  def satisfied (r : Rule) (i : I) := r.reduct_satisfied i i
end Rule

instance : has_mem Rule Program := ⟨@list.mem Rule⟩ 
namespace Program
  structure reduct_model (self : Program) (i_pos i_neg : I) : Prop :=
    (p : ∀r ∈ self, Rule.reduct_satisfied r i_pos i_neg)
  def model (self : Program) (i : I) := self.reduct_model i i
  structure stable_model (self : Program) (i : I) : Prop :=
    (m : self.model i)
    (p : ∀ii < i, ¬(self.reduct_model ii i))

  def atoms (p : Program) : set atom := {
    a : atom | ∃ (r : Rule) (m : r ∈ p), a = r.head ∨ a ∈ r.pbody ∨ a ∈ r.nbody
  }


  def atoms_list : Program -> list atom
  | [] := []
  | (r::tl) := (r.head::(r.pbody ++ r.nbody)) ++ (atoms_list tl)

lemma atoms_atoms_list_mem_iff {p : Program} (a : atom) : a ∈ p.atoms ↔ a ∈ p.atoms_list := begin     split; assume h,     induction p,      cases h, cases h_h, change false at h_h_w,     contradiction,     cases h with r h2, cases h2 with r_mem acond,     cases r_mem,     unfold atoms_list,     cases acond,     rw [<-r_mem, acond],     exact list.mem_cons_self r.head ((r.pbody ++ r.nbody).append (atoms_list p_tl)),     cases acond; right; rw <-r_mem,     change a ∈ ((r.pbody ++ r.nbody) ++ (atoms_list p_tl)),     rw list.mem_append_eq, left, rw list.mem_append_eq, left,     exact acond,     change a ∈ ((r.pbody ++ r.nbody) ++ (atoms_list p_tl)),     rw list.mem_append_eq, left, rw list.mem_append_eq, right,     exact acond, right,     change a ∈ ((p_hd.pbody ++ p_hd.nbody) ++ (atoms_list p_tl)),     change r ∈ p_tl at r_mem,     rw list.mem_append_eq, right,     refine p_ih _,     exact Exists.intro r (Exists.intro r_mem acond),     induction p, change false at h, contradiction,     cases h,     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     exact or.inl h,     change a ∈ ((p_hd.pbody ++ p_hd.nbody) ++ (atoms_list p_tl)) at h,     repeat {rw list.mem_append_eq at h},     repeat {cases h},     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     right, left, exact h,     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     right, right, exact h,     have h2 := p_ih h,     cases h2 with r h3, cases h3 with rmem acond,     have rmem2 : r ∈ p_hd :: p_tl := list.mem_of_mem_tail rmem,     exact Exists.intro r (Exists.intro rmem2 acond),   end 

instance program_atom_mem_decidable {p : Program} {a : atom} : decidable (a ∈ p.atoms) := begin
  rw (@atoms_atoms_list_mem_iff p a),
  exact @list.decidable_mem atom atom.decidable_eq a p.atoms_list
end 


-- lemma external_atom (p : Program) : ∃ a : atom, a ∉ p.atoms := sorry

  -- An interpretation bound to a program p
  @[ext]
  structure I (p : Program) :=
    (e : Π (a : atom) (m : a ∈ p.atoms), tv)


end Program

def Program.localize (p : Program) (i : I) : p.I := ⟨λ a amem, i a⟩ 
def Program.I.i {p : Program} (pi : p.I) : I := λ a, (dite (a ∈ p.atoms)
  (λ c, pi.e a c)
  (λ a, vfalse))






namespace Program
  @[simp] lemma I_eq_PI {p : Program} (pi : p.I) : (p.localize (pi.i)) = pi := begin
    ext a amem,
    change dite (a ∈ p.atoms) (λ (c : a ∈ p.atoms), pi.e a c) (λ (a : a ∉ p.atoms), vfalse) = pi.e a amem,
    split_ifs, refl,
  end
  lemma I.i.inj {p : Program} : function.injective (@Program.I.i p) := begin
    assume pi1 pi2 pii_eq,
    ext a amem,
    rw [<-I_eq_PI pi1, <-I_eq_PI pi2, pii_eq],
  end
end Program

instance {p : Program} : has_coe p.I I := ⟨Program.I.i⟩
instance {p : Program} : has_coe_to_fun p.I (λ _, I) := ⟨Program.I.i⟩
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

instance {p : Program} : has_coe (set p.I) (set I) := ⟨set.image Program.I.i⟩

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

lemma Program.I.Inf_insert_top_outside { p : Program } {S : set p.I} : p.localize (I.Inf (Program.I.i '' S)) = p.localize (I.Inf (insert (@Program.I.top p) (Program.I.i '' S))) := begin
sorry,
end


lemma Program.I.Inf_insert {p : Program} {S : set p.I} : p.localize (I.Inf (Program.I.i '' S)) = p.localize (I.Inf (Program.I.i '' (insert ⊤ S))) := begin
  have top_outside : p.localize (I.Inf (Program.I.i '' S)) = p.localize (I.Inf (insert Program.I.top (Program.I.i '' S))) := Program.I.Inf_insert_top_outside,
  rw top_outside,
  ext, unfold I.Inf,
  have wo_Inf : (λ (i : I), i x) '' insert (@Program.I.top p) (Program.I.i '' S) = (λ (i : I), i x) '' (Program.I.i '' (insert ⊤ S)) := begin
    ext, unfold_coes, simp, split; assume h,
    cases h with x2, 
    have x_pi := p.localize x2,
    cases h_h, cases h_h_left,
    have l : p.localize x2 = ⊤ := begin
      rw [h_h_left, Program.I_eq_PI], refl,
    end,
    refine Exists.intro (p.localize x2) _,
    refine (and.intro (or.inl l) _),
    rw [<-h_h_right, h_h_left, <-h_h_left, l, h_h_left], refl,
    cases h_h_left with pi foo,
    refine Exists.intro pi (and.intro (or.inr foo.left) _),
    rw [foo.right, h_h_right],
    cases h with pi cond,
    cases cond, cases cond_left,
    refine Exists.intro pi.i _, split, left,
    rw cond_left, refl,
    exact cond_right,
    refine Exists.intro pi.i (and.intro (or.inr _) _),
    exact Exists.intro pi (and.intro cond_left rfl),
    exact cond_right,
  end,
  unfold Program.localize, simp,
  rw wo_Inf,
end

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




  -- @[reducible] noncomputable instance complete_lattice : complete_lattice I := {
  --   le := I.le,
  --   sup := I.sup,
  --   sup_le := I.sup_le,
  --   le_sup_right := I.le_sup_right,
  --   le_sup_left := I.le_sup_left,
  --   inf := I.inf,
  --   le_inf := I.le_inf,
  --   inf_le_right := I.inf_le_right,
  --   inf_le_left := I.inf_le_left,
  --   Sup := I.Sup,
  --   le_Sup := I.le_Sup,
  --   Sup_le := I.Sup_le,
  --   Inf := I.Inf,
  --   le_Inf := I.le_Inf,
  --   Inf_le := I.Inf_le,
  --   ..I.partial_order,
  --   ..I.bounded_order,
  -- }

