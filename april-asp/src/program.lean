/-
Defines a normal ASP program and its three-valued semantics
-/

import primitives
import misc
import .complete_lattice.I
import order.fixed_points
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

  instance Program.has_subset : has_subset Program := list.has_subset

  lemma subset_atoms_subset (p : Program) {p' : Program} (ss : p ⊆ p') : p.atoms ⊆ p'.atoms := λ a amem, begin
    cases amem with r b, cases b with rmem,
    exact Exists.intro r (Exists.intro (ss rmem) b_h),
  end

  def atoms_list : Program -> list atom
  | [] := []
  | (r::tl) := (r.head::(r.pbody ++ r.nbody)) ++ (atoms_list tl)

  lemma atoms_atoms_list_mem_iff {p : Program} (a : atom) : a ∈ p.atoms ↔ a ∈ p.atoms_list := begin     split; assume h,     induction p,      cases h, cases h_h, change false at h_h_w,     contradiction,     cases h with r h2, cases h2 with r_mem acond,     cases r_mem,     unfold atoms_list,     cases acond,     rw [<-r_mem, acond],     exact list.mem_cons_self r.head ((r.pbody ++ r.nbody).append (atoms_list p_tl)),     cases acond; right; rw <-r_mem,     change a ∈ ((r.pbody ++ r.nbody) ++ (atoms_list p_tl)),     rw list.mem_append_eq, left, rw list.mem_append_eq, left,     exact acond,     change a ∈ ((r.pbody ++ r.nbody) ++ (atoms_list p_tl)),     rw list.mem_append_eq, left, rw list.mem_append_eq, right,     exact acond, right,     change a ∈ ((p_hd.pbody ++ p_hd.nbody) ++ (atoms_list p_tl)),     change r ∈ p_tl at r_mem,     rw list.mem_append_eq, right,     refine p_ih _,     exact Exists.intro r (Exists.intro r_mem acond),     induction p, change false at h, contradiction,     cases h,     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     exact or.inl h,     change a ∈ ((p_hd.pbody ++ p_hd.nbody) ++ (atoms_list p_tl)) at h,     repeat {rw list.mem_append_eq at h},     repeat {cases h},     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     right, left, exact h,     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     right, right, exact h,     have h2 := p_ih h,     cases h2 with r h3, cases h3 with rmem acond,     have rmem2 : r ∈ p_hd :: p_tl := list.mem_of_mem_tail rmem,     exact Exists.intro r (Exists.intro rmem2 acond),   end 

  instance program_atom_mem_decidable {p : Program} {a : atom} : decidable (a ∈ p.atoms) := begin
    rw (@atoms_atoms_list_mem_iff p a),
    exact @list.decidable_mem atom atom.decidable_eq a p.atoms_list
  end 

  instance program_forall_atom_mem_decidable (p : Program) {prop : atom -> Prop} [decidable_pred prop] : decidable (∀ a ∈ p.atoms, prop a) := begin
    by_cases ∀ a ∈ p.atoms_list, prop a,
    apply decidable.is_true, intros a amem, 
    exact h a ((atoms_atoms_list_mem_iff a).mp amem),
    apply decidable.is_false, simp at |- h, cases h with x,
    refine Exists.intro x (and.intro ((atoms_atoms_list_mem_iff x).mpr h_h.left) h_h.right),
  end

  instance program_exists_atom_mem_decidable (p : Program) {prop : atom -> Prop} [decidable_pred prop] : decidable (∃ a ∈ p.atoms, prop a) := begin
    by_cases ∀ a ∈ p.atoms, ¬prop a,
    apply decidable.is_false, simp, exact h,
    apply decidable.is_true, simp at h, exact bex_def.mpr h,
  end
end Program



def localize (p : Program) (i : I) : I := λ a, if a ∈ p.atoms then i a else vfalse
lemma localize.monotone {p : Program} : monotone $ localize p := λ _ _ c, I.less_than_or_equal.mk (λ a, by {unfold localize, split_ifs, exact c.p a, exact rfl.le})
def Program.localize (p : Program) : I →o I := ⟨localize p, localize.monotone⟩
def Program.I (p : Program) := { i : I // p.localize i = i }
@[reducible] noncomputable instance Program.I.complete_lattice {p : Program} : complete_lattice p.I := fixed_points.function.fixed_points.complete_lattice p.localize
lemma Program.localize_single_fixedpoint {p : Program} {i : I} : p.localize (p.localize i) = p.localize i := by {ext, unfold_coes, simp, unfold_coes, unfold Program.localize, simp, unfold localize, split_ifs, all_goals {refl}}
def Program.I.mk {p : Program} (i : I) : p.I := subtype.mk (p.localize i) Program.localize_single_fixedpoint
-- p.localize pi.val carries more info and may be more convenient. 
-- Program.I.ext validates the correctness of this choice
instance {p : Program} : has_coe_to_fun p.I (λ _, I) := ⟨λ pi, p.localize pi.val⟩
@[ext] lemma Program.I.ext {p : Program} {i ii : p.I} : (∀ a : atom, i a = ii a) ↔ i = ii := begin
  have i_prop := i.prop, unfold_coes at i_prop, 
  have ii_prop := ii.prop, unfold_coes at ii_prop, 
  split; intro h, unfold_coes at h,
  rw [i_prop, ii_prop] at h,
  ext, unfold_coes, exact h x,
  intro a, unfold_coes,
  rw [function.funext_iff.mp i_prop a, function.funext_iff.mp ii_prop a],
  exact congr_fun (congr_arg subtype.val h) a,
end
lemma Program.I.not_mem_atom_vfalse {p : Program} {pi : p.I} {a : atom} (anmem : a ∉ p.atoms) : pi a = vfalse := by { unfold_coes, unfold Program.localize, simp, unfold localize, split_ifs, refl }

instance Program.has_subset : has_subset Program := list.has_subset

instance {p : Program} : decidable_eq p.I := begin
  intros i1 i2,
  by_cases ∀ a ∈ p.atoms, i1 a = i2 a,
  apply decidable.is_true,
  apply Program.I.ext.mp, intro a,
  by_cases h2 : a ∈ p.atoms, exact h a h2,
  repeat {rw Program.I.not_mem_atom_vfalse h2},
  apply decidable.is_false,
  simp at h, rw <-Program.I.ext, simp, cases h with c,
  exact Exists.intro c h_h.right,
end

namespace Rule
  lemma atom_program_mem_pbody {p : Program} (r : Rule) (rmem : r ∈ p) (a : atom) : a ∈ r.pbody -> a ∈ p.atoms := λ h, begin
    refine Exists.intro r (Exists.intro rmem _),
    right, left, exact h,
  end
  lemma atom_program_mem_nbody {p : Program} (r : Rule) (rmem : r ∈ p) (a : atom) : a ∈ r.nbody -> a ∈ p.atoms := λ h, begin
    refine Exists.intro r (Exists.intro rmem _),
    right, right, exact h,
  end

end Rule
