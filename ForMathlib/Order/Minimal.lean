import Mathlib.Order.Minimal

variable {α : Type _} {r : α → α → Prop} {s : Set α} {x : α} {P : α → Prop}

theorem mem_maximals_iff' [IsAntisymm α r] :
    x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y :=
  by
  simp only [maximals, Set.mem_sep_iff, and_congr_right_iff]
  refine' fun hx => ⟨fun h y hys hxy => antisymm hxy (h hys hxy), fun h y hys hxy => _⟩
  convert hxy <;> rw [h hys hxy]

theorem mem_maximals_prop_iff [IsAntisymm α r] :
    x ∈ maximals r P ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
  mem_maximals_iff'

theorem mem_maximals_setOf_iff [IsAntisymm α r] :
    x ∈ maximals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
  mem_maximals_iff'

