import Mathlib.Data.Set.Image

open Set

variable {α β : Type _} {f : α → β}

theorem Function.Injective.image_compl_eq (hf : f.Injective) {A : Set α} :
    f '' Aᶜ = range f \ f '' A := by rw [← image_univ, ← image_diff hf, compl_eq_univ_diff]

theorem Function.Injective.preimage_subset_of_subset_image (hf : f.Injective) {A : Set α}
    {B : Set β} (h : B ⊆ f '' A) : f ⁻¹' B ⊆ A :=
  by
  convert preimage_mono h
  rw [preimage_image_eq _ hf]

theorem Function.Injective.image_eq_singleton_iff (hf : f.Injective) {A : Set α} {b : β} :
    f '' A = {b} ↔ ∃ a, f a = b ∧ A = {a} :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain rfl | ⟨a, rfl⟩ :=
      (subsingleton_of_image hf A
          (by
            rw [h]
            exact subsingleton_singleton)).eq_empty_or_singleton
    · rw [image_empty] at h
      exact (singleton_ne_empty _ h.symm).elim
    exact ⟨_, by simpa using h, rfl⟩
  rintro ⟨a, rfl, rfl⟩
  rw [image_singleton]

@[simp]
theorem Subtype.preimage_image_coe (s : Set α) (x : Set s) :
    (coe ⁻¹' (coe '' x : Set α) : Set s) = x :=
  preimage_image_eq x Subtype.coe_injective

@[simp]
theorem Subtype.image_coe_subset_image_coe_iff (s : Set α) (x y : Set s) :
    (coe '' x : Set α) ⊆ coe '' y ↔ x ⊆ y :=
  image_subset_image_iff Subtype.coe_injective

@[simp]
theorem Subtype.image_coe_eq_image_coe_iff (s : Set α) (x y : Set s) :
    (coe '' x : Set α) = coe '' y ↔ x = y :=
  image_eq_image Subtype.coe_injective

