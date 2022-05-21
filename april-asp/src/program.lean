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


  def atoms_list : Program -> list atom
  | [] := []
  | (r::tl) := (r.head::(r.pbody ++ r.nbody)) ++ (atoms_list tl)

  lemma atoms_atoms_list_mem_iff {p : Program} (a : atom) : a ∈ p.atoms ↔ a ∈ p.atoms_list := begin     split; assume h,     induction p,      cases h, cases h_h, change false at h_h_w,     contradiction,     cases h with r h2, cases h2 with r_mem acond,     cases r_mem,     unfold atoms_list,     cases acond,     rw [<-r_mem, acond],     exact list.mem_cons_self r.head ((r.pbody ++ r.nbody).append (atoms_list p_tl)),     cases acond; right; rw <-r_mem,     change a ∈ ((r.pbody ++ r.nbody) ++ (atoms_list p_tl)),     rw list.mem_append_eq, left, rw list.mem_append_eq, left,     exact acond,     change a ∈ ((r.pbody ++ r.nbody) ++ (atoms_list p_tl)),     rw list.mem_append_eq, left, rw list.mem_append_eq, right,     exact acond, right,     change a ∈ ((p_hd.pbody ++ p_hd.nbody) ++ (atoms_list p_tl)),     change r ∈ p_tl at r_mem,     rw list.mem_append_eq, right,     refine p_ih _,     exact Exists.intro r (Exists.intro r_mem acond),     induction p, change false at h, contradiction,     cases h,     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     exact or.inl h,     change a ∈ ((p_hd.pbody ++ p_hd.nbody) ++ (atoms_list p_tl)) at h,     repeat {rw list.mem_append_eq at h},     repeat {cases h},     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     right, left, exact h,     refine Exists.intro p_hd (Exists.intro (list.mem_cons_self p_hd p_tl) _),     right, right, exact h,     have h2 := p_ih h,     cases h2 with r h3, cases h3 with rmem acond,     have rmem2 : r ∈ p_hd :: p_tl := list.mem_of_mem_tail rmem,     exact Exists.intro r (Exists.intro rmem2 acond),   end 

  instance program_atom_mem_decidable {p : Program} {a : atom} : decidable (a ∈ p.atoms) := begin
    rw (@atoms_atoms_list_mem_iff p a),
    exact @list.decidable_mem atom atom.decidable_eq a p.atoms_list
  end 

  -- @[ext]
  -- structure I (p : Program) :=
  --   (e : Π (a : atom) (m : a ∈ p.atoms), tv)
end Program



def localize (p : Program) (i : I) : I := λ a, if a ∈ p.atoms then i a else vfalse
lemma localize.monotone {p : Program} : monotone $ localize p := λ _ _ c, I.less_than_or_equal.mk (λ a, begin
  unfold localize, split_ifs,
  exact c.p a, exact rfl.le,
end)
def Program.localize (p : Program) : I →o I := ⟨localize p, localize.monotone⟩



variable p : Program

def Program.I (p : Program) := { i : I // i = p.localize i }
lemma Program.localize_single_app_fixedpoint {p : Program} {i : I} : p.localize i = p.localize (p.localize i) := begin
  ext, unfold_coes, simp, unfold_coes, unfold Program.localize, simp, unfold localize, split_ifs, all_goals {refl},
end
lemma all_fixedpoints {p : Program} : function.fixed_points (p.localize) == G := begin

end
def Program.I.mk {p : Program} (i : I) : p.I := subtype.mk (p.localize i) Program.localize_single_app_fixedpoint

#check subtype.mk


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

