import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Sigma
import Mathlib.Logic.Pairwise

/-! Some lemmas about sets in sigma types -/


open Set

namespace Sigma

variable {ι : Type _} {α : ι → Type _} {x y : Set (Σi, α i)} {f : ∀ i, Set (α i)} {i j : ι}

theorem subset_iff : x ⊆ y ↔ ∀ i, Sigma.mk i ⁻¹' x ⊆ Sigma.mk i ⁻¹' y :=
  ⟨fun h i a ha => h ha, fun h ⟨i, a⟩ ha => h i ha⟩

theorem eq_iff_forall_preimage_mk_eq : x = y ↔ ∀ i, Sigma.mk i ⁻¹' x = Sigma.mk i ⁻¹' y :=
  ⟨by
    rintro rfl
    exact fun _ => rfl, fun h =>
    (Sigma.subset_iff.mpr fun i => (h i).Subset).antisymm
      (Sigma.subset_iff.mpr fun i => (h i).symm.Subset)⟩

@[simp]
theorem preimage_mk_iUnion_image_mk : (Sigma.mk j ⁻¹' ⋃ i, Sigma.mk i '' f i) = f j :=
  by
  rw [preimage_Union, subset_antisymm_iff, Union_subset_iff]
  refine' ⟨fun k => _, subset_Union_of_subset j (by rw [preimage_image_eq _ sigma_mk_injective])⟩
  obtain rfl | hjk := eq_or_ne j k
  · rw [preimage_image_eq _ sigma_mk_injective]
  rw [preimage_image_sigma_mk_of_ne hjk]
  exact empty_subset _

theorem eq_iUnion_image_preimage_mk (x : Set (Σi, α i)) :
    x = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' x) := by simp [Sigma.eq_iff_forall_preimage_mk_eq]

theorem image_preimage_mk_pairwise_disjoint (x : Set (Σi, α i)) :
    Pairwise (Disjoint on fun i => Sigma.mk i '' (Sigma.mk i ⁻¹' x)) :=
  by
  refine' fun i j hij s hs hs' a ha => hij _
  simp only [bot_eq_empty, le_eq_subset, mem_empty_iff_false] at hs hs'⊢
  obtain ⟨t, ht, rfl⟩ := hs ha
  obtain ⟨t', ht', h'⟩ := hs' ha
  simp only at h'
  rw [h'.1]

end Sigma

theorem Equiv.sigmaEquivProd_sigma_mk {ι α : Type _} {i : ι} :
    Equiv.sigmaEquivProd ι α ∘ Sigma.mk i = Prod.mk i := by ext <;> simp

