
import data.fintype.order
import data.nat.basic -- Some basic simps
import order.complete_lattice
open list


set_option trace.simplify.rewrite true


inductive tv
| vtrue
| vundef
| vfalse
open tv

namespace tv
@[simp] def to_nat (a : tv) : ℕ := tv.cases_on a 3 2 1
@[simp] lemma tv_unnat_eq {a b : tv} : (tv.to_nat a) = (tv.to_nat b) <-> a = b :=  begin
    split, all_goals { assume h, cases a; cases b; simp at |- h; contradiction },
end


@[reducible] def le (a b : tv) : Prop := nat.le (tv.to_nat a) (tv.to_nat b)
@[reducible] def lt (a b : tv) : Prop := nat.lt (tv.to_nat a) (tv.to_nat b)
instance : has_le tv := ⟨le⟩
instance : has_lt tv := ⟨lt⟩

-- Lemmas for the linear order on tv
-- that uses the mapping to_nat and the standard linear ordering on nat
@[refl] lemma le_refl (a : tv) : a <= a := nat.le_refl (tv.to_nat a)
@[trans] lemma le_trans {n m k : tv} (h1 : n ≤ m) : m ≤ k → n ≤ k := λ h2, nat.le_trans h1 h2
lemma le_antisymm {n m : tv} (h1 : n ≤ m) : m ≤ n → n = m :=  λ h2, tv_unnat_eq.mp (nat.le_antisymm h1 h2)
lemma le_total {m n : tv} : m ≤ n ∨ n ≤ m := nat.le_total
lemma lt_iff_le_not_le {m n : tv} : m < n ↔ (m ≤ n ∧ ¬ n ≤ m) := nat.lt_iff_le_not_le 
instance decidable_lt : ∀ a b : tv, decidable (a < b) := λ a b, nat.decidable_lt (tv.to_nat a) (tv.to_nat b)
instance decidable_le : ∀ a b : tv, decidable (a ≤ b):= λ a b, nat.decidable_le (tv.to_nat a) (tv.to_nat b)
instance decidable_eq : decidable_eq tv := λ a b, by { rw <- tv_unnat_eq, apply nat.decidable_eq }
instance linear_order : linear_order tv :=
{ le := le,
  le_refl := tv.le_refl,
  le_trans := @tv.le_trans,
  le_antisymm := @tv.le_antisymm,
  le_total := @tv.le_total,
  lt := lt,
  lt_iff_le_not_le := @tv.lt_iff_le_not_le,
  decidable_le               := tv.decidable_le,
  -- These fields are optional but easy enough to define
  decidable_lt               := tv.decidable_lt,
  decidable_eq               := tv.decidable_eq }

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





def atom := ℕ

def I := atom -> tv

structure I_less_than_or_equal  (i1 : I) (i2 : I) : Prop :=
  (p : Π a : atom, (i1 a) <= (i2 a))

instance : has_le I := ⟨I_less_than_or_equal⟩
structure I_less_than (i1 : I) (i2 : I) : Prop :=
  (p : i1 <= i2) (q : ∃a : atom, (i1 a) < (i2 a))
instance : has_lt I := ⟨I_less_than⟩ 
lemma I_not_lt_exists {i1 i2 : I} (h : ¬i1 <= i2) : ∃ a : atom, (i2 a) < (i1 a) := begin
  by_contradiction exis,
  rw not_exists at exis,
  -- Not sure why I can't write simp as `rw not_lt at exis`
  -- not_lt relies on tv.linear_order so it's probably doing the conversion but not tracing it
  simp at exis,
  have le : i1 <= i2 := ⟨ exis ⟩,
  exact h le,
end

namespace I
def le (i1 i2 : I) := I_less_than_or_equal i1 i2
def lt (i1 i2 : I) := I_less_than i1 i2
@[refl] lemma le_refl (i : I) : i <= i := ⟨λ a, tv.le_refl (i a)⟩ 
@[trans] lemma le_trans {a b c : I} (h1 : a ≤ b) : b ≤ c → a ≤ c := λ h2, ⟨λ a, tv.le_trans (h1.p a) (h2.p a)⟩
lemma le_antisymm {n m : I} (h1 : n <= m) : m <= n -> n = m := λ h2, funext (λ a : atom, tv.le_antisymm (h1.p a) (h2.p a))
lemma lt_iff_le_not_le {a b : I} : a < b ↔ (a ≤ b ∧ ¬ b ≤ a) := iff.intro
  (λ l, begin
    split, exact l.p,
    by_contradiction p,
    cases l.q with w kk,
    exact ((lt_iff_le_not_le.mp kk).right) (p.p w) end)
  (λ r, begin
    split, exact r.left,
    exact I_not_lt_exists r.right,
  end)
instance partial_order : partial_order I :=
{ le := le,
  lt := lt,
  le_refl := le_refl,
  le_trans := @le_trans,
  le_antisymm := @le_antisymm,
  lt_iff_le_not_le := @lt_iff_le_not_le }


def top (a : atom) : tv := vtrue
lemma le_top (i : I) : i <= I.top := I_less_than_or_equal.mk (λ a : atom, tv.le_top (i a))
def bot (a : atom) : tv := vfalse
lemma bot_le (i : I) : I_less_than_or_equal I.bot i := I_less_than_or_equal.mk (λ a, tv.bot_le (i a))


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

--  ∀ (s : set α) (a : α), a ∈ s → a ≤ complete_lattice.Sup s

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
  le_Sup := le_Sup,
  Sup_le := Sup_le,
  Inf := I.Inf,
  le_Inf := I.le_Inf,
  Inf_le := I.Inf_le,
  ..I.partial_order,
  ..I.bounded_order,
}


end I
------- RULES AND PROGRAM and stuff



namespace tv
def conj (l : list tv) : tv := foldl tv.inf tv.vtrue l
-- Logical disjunction of a list of truth values
def disj (l : list tv) : tv := foldl tv.sup tv.vfalse l
-- Logical complement of a list of truth values
@[simp, reducible] def negate (v : tv) : tv := tv.cases_on v tv.vfalse tv.vundef tv.vtrue
instance : has_neg tv := ⟨negate⟩ 
def neg (l : list tv) : list tv := map tv.negate l
end tv


namespace I
def eval (self : I) (atoms : list atom) : list tv := map self atoms
def assign (self : I) (a : atom) (v : tv) : I := λ b, if a = b then v else self a
end I


structure Rule :=
  (head : atom)
  (pbody : list atom)
  (nbody : list atom)
namespace Rule
  def atoms (self : Rule) : list atom :=
    self.head :: (self.pbody ++ self.nbody)
  def eval_pbody (self : Rule) (i : I) : tv := tv.conj (i.eval self.pbody) 
  def eval_nbody (self : Rule) (i : I) : tv := tv.conj (tv.neg (i.eval self.nbody))
  def eval_body (self : Rule) (i : I) : tv := (self.eval_pbody i) ⊓ (self.eval_nbody i)
  def eval_head (self : Rule) (i : I) : tv := i self.head




  -- FACK section

  lemma foldl_min_simplify {hd : tv} {tl : list tv} : foldl min ⊤ (hd::tl) = foldl min hd tl := by { simp }

  lemma foldl_min_extract {a : tv} {l : list tv} : foldl min a l = min a (foldl min ⊤ l) := begin
    cases l, simp,
    rw foldl_min_simplify,
    unfold foldl, 
    exact foldl_assoc,
  end

  -- faaaaack
  -- Don't think I need this
  lemma fack {l : list tv} {a : tv} : foldl min ⊤ (a::l) <= foldl min ⊤ l := begin
    simp at *,
    have y : foldl min a l = min a (foldl min ⊤ l) := begin
      exact foldl_min_extract,
    end,
    rw y,
    cases foldl min ⊤ l,
    all_goals{ simp } 
  end


  @[simp] def eval_pbody_monotone (r: Rule) : monotone r.eval_pbody := λ a b c, begin
    unfold Rule.eval_pbody,
    -- unfold tv.conj,
    induction r.pbody,
    exact rfl.ge,
    have mm : a hd <= b hd := c.p hd,
    -- suggest [f, f2],
    -- have dd := f (a.eval tl) (a hd),
    unfold tv.conj at |- ih,
    unfold tv.inf at |- ih,
    rw foldl_min_extract,
    -- TODO this might complete it, but need to factor out the head from I.eval
    -- Eg. a.eval h::l = a h :: (a.eval l)
    -- Might need to repeat a few things that can be applied multiple times
    have q : a.eval (hd::tl) = a hd :: (a.eval tl) := sorry,
    rw q,
    rw foldl_min_simplify,
    -- unfold I.eval,

    -- cases (a.eval (hd :: tl)); cases (b.eval (hd :: tl)),
    -- simp,
    -- suggest,
  end

  @[simp] def eval_nbody_monotone (r: Rule) : monotone r.eval_nbody := λ a b c, begin
    sorry
  end
  @[simp] def eval_body_monotone (r: Rule) : monotone r.eval_body := 
    λ a b c, min_le_min (eval_pbody_monotone r c) (eval_nbody_monotone r c)

  structure satisfied (r : Rule) (i : I) : Prop :=
    (p : r.eval_body i <= r.eval_head i)
end Rule

def Program := list Rule
instance : has_mem Rule Program := ⟨@list.mem Rule⟩ 
namespace Program
  structure model (self : Program) (i : I) : Prop :=
    (p : ∀r ∈ self, Rule.satisfied r i)
  structure stable_model (self : Program) (i : I) : Prop :=
    (m : self.model i)
    (p : ∀ii <= i, ¬(self.model i))
end Program

def xT_propagate (i : I) : Program -> I
| [] := i
| (r::p) := (i.assign r.head (r.eval_body i)) ⊔ (xT_propagate p)


def T_propagate (p : Program) (i : I) : I := xT_propagate i p



theorem T_monotone (p : Program) : monotone (T_propagate p) := λ a b c, begin
refine I_less_than_or_equal.mk _,
assume atom,
unfold T_propagate,
induction p,
exact c.p atom,
unfold xT_propagate,
refine sup_le_sup _ p_ih,
unfold I.assign,
split_ifs,
exact p_hd.eval_body_monotone c,
exact c.p p_hd.head,
-- unfold Rule.eval_body Rule.eval_pbody Rule.eval_nbody,
end
