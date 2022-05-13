/- General proofs not specific to ASP -/

import order.complete_lattice

lemma Inf_insert_top {α : Type} [complete_lattice α] {S : set α) : Inf S = Inf (insert ⊤ S) := by {
  rw Inf_insert, exact le_antisymm (le_inf le_top rfl.le) inf_le_right
}

lemma Sup_insert_bot {α : Type} [complete_lattice α] (S : set α) : Sup S = Sup (insert ⊥ S) := by {
  rw Sup_insert, exact le_antisymm le_sup_right (sup_le bot_le rfl.le),
}