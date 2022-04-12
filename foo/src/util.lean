
import init.data.list.lemmas

variable {α : Type}

open list

#check subset_of_cons_subset
structure sublist  (α : Type) (ll : list α) :=
(l : list α)
(p: l ⊆ ll)

def filter (p : α → Prop) [decidable_pred p] : list α → list α
| []     := []
| (a::l) := if p a then a :: filter l else filter l

def filter_sublist (p : α → Prop) [decidable_pred p] : (Π l: list α,  sublist α l)
| l : [] := sorry

end


lemma shrink_sublist_type {l ll : list α} (s : l ⊆ ll) (f : sublist α ll -> sublist α ll) : sublist α l -> sublist α l :=
(λ x,
sorry)

private def filter_sublist_helper (p : α → Prop) [decidable_pred p] (ll : list α) : sublist α ll -> sublist α ll
| ⟨[], s⟩  := ⟨[], s⟩
| ⟨a::l, s⟩ := begin
  let smol : sublist α l := ⟨l, list.subset.refl l⟩, 
  let h : l ⊆ ll := subset_of_cons_subset s,
  have r := shrink_sublist_type h filter_sublist_helper, 
  have rest := (r smol),

  have f := if p a then begin
    let l := a :: rest.l,

  end
end

-- if p a then a :: (filter_sublist_helper ⟨l, list.subset_of_cons_subset s⟩) else sorry

