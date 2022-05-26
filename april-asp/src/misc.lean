/- General proofs not specific to ASP -/

import order.complete_lattice

lemma Inf_insert_top {α : Type} [complete_lattice α] (S : set α) : Inf S = Inf (insert ⊤ S) := by {
  rw Inf_insert, exact le_antisymm (le_inf le_top rfl.le) inf_le_right
}

lemma Sup_insert_bot {α : Type} [complete_lattice α] (S : set α) : Sup S = Sup (insert ⊥ S) := by {
  rw Sup_insert, exact le_antisymm le_sup_right (sup_le bot_le rfl.le),
}

lemma bin_eq_bin_split {α : Type} {β : Type} {f : α -> α -> β} {a b c d : α} : a = c ∧ b = d -> f a b = f c d := λ a, by { rw [a.left, a.right] }

lemma inf_eq_inf_split {α : Type} [hi : has_inf α] {a b c d : α} : a = c ∧ b = d -> a ⊓ b = c ⊓ d := @bin_eq_bin_split α α hi.inf a b c d
