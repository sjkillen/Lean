import ..primitives
open tv

namespace I
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

  lemma le_top (i : I) : i <= I.top := I.less_than_or_equal.mk (λ a : atom, tv.le_top (i a))
  lemma bot_le (i : I) : I.less_than_or_equal I.bot i := I.less_than_or_equal.mk (λ a, tv.bot_le (i a))

  instance bounded_order : bounded_order I := {
    top := I.top,
    le_top := I.le_top,
    bot := I.bot,
    bot_le := I.bot_le,
  }

  instance has_sup : has_sup I := ⟨I.sup⟩
  @[simp] lemma sup_le (a b c : I) : a <= c -> b <= c -> a ⊔ b <= c := (λ h g, ⟨(λ x, max_le (h.p x) (g.p x))⟩)
  @[simp] lemma le_sup_right (a b : I) : b <= a ⊔ b := ⟨λ x, le_max_right (a x) (b x)⟩
  @[simp] lemma le_sup_left (a b : I) : a <= a ⊔ b  := ⟨λ x, le_max_left (a x) (b x)⟩

  instance has_inf : has_inf I := ⟨I.inf⟩
  @[simp] lemma le_inf (a b c : I) : a <= b -> a <= c -> a <= b ⊓ c := (λ h g, ⟨(λ x, le_min (h.p x) (g.p x))⟩)
  @[simp] lemma inf_le_right (a b : I) : a ⊓ b <= b:= ⟨λ x, min_le_right (a x) (b x)⟩
  @[simp] lemma inf_le_left (a b : I) : a ⊓ b <= a  := ⟨λ x, min_le_left (a x) (b x)⟩

  @[reducible] 
  noncomputable instance has_Sup : has_Sup I := ⟨I.Sup⟩
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