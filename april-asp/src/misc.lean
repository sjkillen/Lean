import order.complete_lattice
open list

#check foldl

-- set_option trace.simplify.rewrite true
-- set_option trace.simplify.rewrite true

@[simp, reducible]
lemma f {α : Type} [lat: complete_linear_order α] (l : list α) (a : α) : foldl min ⊥ (a::l) <= foldl min ⊥ l := by { simp }
@[simp, reducible]
lemma f2 {α : Type} [lat: complete_linear_order α] (l : list α) (a : α) : foldl max ⊤ l <= foldl max ⊤ (a::l) := by { simp }
