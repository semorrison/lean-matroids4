import Project.Mathlib.FinsumNcard
import Project.Mathlib.Data.Set.Image
import Project.Mathlib.Logic.Equiv.Basic
import Matroid.Constructions.Basic
import Matroid.Maps.Equiv

noncomputable section

open Set Function Sigma

open Classical

open BigOperators

namespace Matroid

universe u v

section DirectSum

variable {ι : Type u} {E : ι → Type v} {M : ∀ i, Matroid (E i)}

/-- The direct sum of an `ι`-indexed collection of matroids `(M i : matroid E i)`. A set is a base
  if and only if its intersection with each matroid is a base -/
def directSum (M : ∀ i, Matroid (E i)) : Matroid (Σi, E i)
    where
  base B := ∀ i : ι, (M i).base (Sigma.mk i ⁻¹' B)
  exists_base' := by
    choose B hB using fun i => (M i).exists_base
    refine' ⟨⋃ i : ι, Sigma.mk i '' B i, fun i => _⟩
    rw [preimage_mk_Union_image_mk]
    exact hB i
  base_exchange' := by
    rintro B₁ B₂ hB₁ hB₂ ⟨j, x⟩ hx
    obtain ⟨y, hy, hBy⟩ := (hB₁ j).exchange (hB₂ j) hx
    refine' ⟨Sigma.mk j y, hy, fun i => _⟩
    · obtain rfl | hne := eq_or_ne i j
      · convert hBy
        ext
        simp
      convert hB₁ i using 1
      rw [← union_singleton, preimage_union, preimage_diff]
      -- ext,
      convert union_empty _
      · ext
        simpa using hne
      convert diff_empty.symm
      ext
      simpa using hne
  maximality := by
    rintro I X ⟨B₀, hB₀, hIB₀⟩ hIX
    have h := fun i =>
      (M i).maximality (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X)
        ⟨Sigma.mk i ⁻¹' B₀, hB₀ i, preimage_mono hIB₀⟩ (preimage_mono hIX)
    choose Js hJs using h
    have h_ex_Bs := fun i => (hJs i).1.1
    choose Bs hBs using h_ex_Bs
    obtain ⟨hBsi, hBsJ⟩ := forall_and_distrib.mp hBs
    set J := ⋃ i, Sigma.mk i '' Js i with Jdef
    set B := ⋃ i, Sigma.mk i '' Bs i with Bdef
    refine' ⟨J, ⟨⟨B, fun i => by simpa using hBsi i, by simpa⟩, _, _⟩, _⟩
    · rintro ⟨i, x⟩ hxJ
      refine' mem_Union_of_mem i (image_subset (Sigma.mk i) (hJs i).1.2.1 (by simpa))
    · refine' Union_subset fun i => _
      rintro x ⟨y, h, rfl⟩
      exact (hJs i).1.2.2 h
    rintro K ⟨⟨BK, hBK, hKBK⟩, ⟨hIK, hKX⟩⟩ hJK ⟨i, x⟩ hxK
    refine'
      mem_Union_of_mem i
        ⟨x, (hJs i).2 ⟨⟨Sigma.mk i ⁻¹' BK, hBK i, _⟩, preimage_mono hIK, preimage_mono hKX⟩ _ hxK,
          rfl⟩
    · exact fun h hy => hKBK hy
    convert preimage_mono hJK
    simp only [preimage_mk_Union_image_mk]

@[simp]
theorem directSum.base_iff {B : Set (Σi, E i)} :
    (directSum M).base B ↔ ∀ i, (M i).base (Sigma.mk i ⁻¹' B) :=
  Iff.rfl

theorem eq_union_image_bases_of_directSum_base {B : Set (Σi, E i)} (h : (directSum M).base B) :
    ∃ Bs : ∀ i, Set (E i), (B = ⋃ i, Sigma.mk i '' Bs i) ∧ ∀ i, (M i).base (Bs i) :=
  ⟨fun i => Sigma.mk i ⁻¹' B, by rw [← eq_Union_image_preimage_mk B], directSum.base_iff.mp h⟩

-- variables [finite ι] [∀ i, finite (E i)]
@[simp]
theorem directSum.indep_iff {I : Set (Σi, E i)} :
    (directSum M).indep I ↔ ∀ i, (M i).indep (Sigma.mk i ⁻¹' I) :=
  by
  simp_rw [indep_iff_subset_base, Sigma.subset_iff, direct_sum.base_iff, preimage_subset_iff,
    mem_preimage]
  refine' ⟨fun ⟨B, hB, hIB⟩ i => ⟨Sigma.mk i ⁻¹' B, hB i, fun a ha => hIB _ _ ha⟩, fun h => _⟩
  choose! f hf using h
  refine' ⟨⋃ i, Sigma.mk i '' f i, fun i => _, fun i a ha => mem_Union_of_mem i _⟩
  · rw [Sigma.preimage_mk_iUnion_image_mk]
    exact (hf i).1
  simpa using (hf i).2 a ha

theorem eq_union_image_indeps_of_directSum_indep {I : Set (Σi, E i)} (h : (directSum M).indep I) :
    ∃ Is : ∀ i, Set (E i), (I = ⋃ i, Sigma.mk i '' Is i) ∧ ∀ i, (M i).indep (Is i) :=
  ⟨fun i => Sigma.mk i ⁻¹' I, by rw [← eq_Union_image_preimage_mk I], directSum.indep_iff.mp h⟩

@[simp]
theorem directSum_basis_iff {I X : Set (Σi, E i)} :
    (directSum M).Basis I X ↔ ∀ i, (M i).Basis (Sigma.mk i ⁻¹' I) (Sigma.mk i ⁻¹' X) :=
  by
  simp_rw [basis_iff, direct_sum.indep_iff]
  refine'
    ⟨fun h i => ⟨h.1 i, preimage_mono h.2.1, fun J hJ hIJ hJX => _⟩, fun h =>
      ⟨fun i => (h i).1, sigma.subset_iff.mpr fun i => (h i).2.1, fun J hJ hIJ hJX => _⟩⟩
  · have h' :=
      h.2.2 (I ∪ Sigma.mk i '' J) (fun j => _) (subset_union_left _ _)
        (union_subset h.2.1 (by simpa))
    · rwa [h', preimage_union, preimage_image_eq _ sigma_mk_injective, union_eq_right_iff_subset]
    obtain rfl | hne := eq_or_ne j i
    ·
      rwa [preimage_union, preimage_image_eq _ sigma_mk_injective,
        union_eq_right_iff_subset.mpr hIJ]
    rw [preimage_union, preimage_image_sigma_mk_of_ne hne, union_empty]
    exact h.1 j
  rw [Sigma.eq_iff_forall_preimage_mk_eq]
  rw [Sigma.subset_iff] at hIJ hJX
  exact fun i => (h i).2.2 _ (hJ _) (hIJ _) (hJX _)

@[simp]
theorem directSum.r_eq [Finite ι] (M : ∀ i, Matroid (E i)) [∀ i, (M i).FiniteRk]
    (X : Set (Σi, E i)) : (directSum M).R X = ∑ᶠ i, (M i).R (Sigma.mk i ⁻¹' X) :=
  by
  obtain ⟨I, hI⟩ := (DirectSum M).exists_basis X
  have hIfin : I.finite :=
    by
    rw [← Set.iUnion_image_preimage_sigma_mk_eq_self I]
    exact finite_Union fun i => finite.image _ (direct_sum.indep_iff.mp hI.indep i).Finite
  -- have hfin : ∀ i, (I i).finite := λ i, by {  },
  rw [← hI.r, hI.indep.r, Sigma.ncard_eq_finsum_ncard_image_preimage_mk _ hIfin]
  rw [direct_sum_basis_iff] at hI
  congr
  ext i
  rw [← (hI i).R, (hI i).indep.R, ncard_image_of_injective _ sigma_mk_injective]

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (j «expr ≠ » i) -/
-- This proof is a bit of a disaster.
@[simp]
theorem directSum.circuit_iff {C : Set (Σi, E i)} :
    (directSum M).Circuit C ↔ ∃ i C₀, (M i).Circuit C₀ ∧ C = Sigma.mk i '' C₀ :=
  by
  refine' ⟨fun hC => _, _⟩
  · have h_dep : ∃ i, ¬(M i).indep (Sigma.mk i ⁻¹' C) :=
      by
      by_contra' h
      rw [← direct_sum.indep_iff] at h
      exact hC.dep h
    obtain ⟨i, hi⟩ := h_dep
    have h_forall : ∀ (j) (_ : j ≠ i), Sigma.mk j ⁻¹' C = ∅ :=
      by
      refine' fun j hj => eq_empty_of_forall_not_mem fun e he => hi _
      have hjC : (⟨j, e⟩ : Σi, E i) ∈ C := he
      convert((direct_sum.indep_iff.mp (hC.diff_singleton_indep hjC)) i).Subset rfl.subset using 1
      rw [preimage_diff, eq_comm]
      convert diff_empty
      convert preimage_image_sigma_mk_of_ne hj.symm {e}
      rw [image_singleton]
    have hC₀ : C = Sigma.mk i '' (Sigma.mk i ⁻¹' C) :=
      by
      nth_rw 1 [← Union_image_preimage_sigma_mk_eq_self C]
      refine' subset_antisymm (Union_subset fun j => _) (subset_Union _ i)
      obtain rfl | hne := eq_or_ne j i
      · exact subset.rfl
      rintro x ⟨h, h', rfl⟩
      exact (not_mem_empty _ ((h_forall _ hne).Subset h')).elim
    refine' ⟨_, _, _, hC₀⟩
    simp_rw [circuit_iff_dep_forall_diff_singleton_indep, direct_sum.indep_iff] at hC⊢
    refine' ⟨hi, fun e he => _⟩
    convert hC.2 ⟨i, e⟩ he i using 1
    ext
    simp
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, direct_sum.indep_iff, not_forall]
  rintro ⟨i, C, ⟨hC, hmin⟩, rfl⟩
  refine' ⟨⟨i, by rwa [preimage_image_eq _ sigma_mk_injective]⟩, _⟩
  rintro ⟨j, e⟩ ⟨f, hf, ⟨h'⟩⟩ j
  rw [preimage_diff]
  obtain rfl | hne := eq_or_ne i j
  · rw [preimage_image_eq _ sigma_mk_injective]
    convert hmin f hf
    ext
    simp
  convert(M j).empty_indep
  rw [preimage_image_sigma_mk_of_ne hne.symm, empty_diff]

@[simp]
theorem directSum.flat_iff {F : Set (Σi, E i)} :
    (directSum M).Flat F ↔ ∀ i, (M i).Flat (Sigma.mk i ⁻¹' F) :=
  by
  simp_rw [flat_iff_forall_circuit, direct_sum.circuit_iff]
  refine'
    ⟨fun h i C e hC heC hss => h (Sigma.mk i '' C) ⟨i, e⟩ ⟨_, _, hC, rfl⟩ ⟨e, heC, rfl⟩ _,
      fun h C e => _⟩
  · simp_rw [diff_singleton_subset_iff, image_subset_iff, ← union_singleton, preimage_union] at hss⊢
    convert hss
    ext
    simp
  rintro ⟨i, C₀, hC₀, rfl⟩ ⟨f, hf, rfl⟩ h'
  refine' h i C₀ f hC₀ hf _
  convert preimage_mono h'
  · rw [preimage_image_eq _ sigma_mk_injective]
  rw [← image_eq_image sigma_mk_injective, image_insert_eq, image_preimage_eq_inter_range,
    image_preimage_eq_inter_range, insert_inter_distrib, insert_eq_of_mem (mem_range_self _)]

end DirectSum

section Sum

variable {ι : Type u} {E₁ E₂ : Type v} {M₁ : Matroid E₁} {M₂ : Matroid E₂}

def sum (M₁ : Matroid E₁) (M₂ : Matroid E₂) : Matroid (Sum E₁ E₂) :=
  (directSum fun i => Bool.casesOn i M₂ M₁ : Matroid (Σb : Bool, cond b E₁ E₂)).congr
    (Equiv.sumEquivSigmaBool E₁ E₂).symm

@[simp]
theorem sum.indep_iff {I : Set (Sum E₁ E₂)} :
    (sum M₁ M₂).indep I ↔ M₁.indep (Sum.inl ⁻¹' I) ∧ M₂.indep (Sum.inr ⁻¹' I) :=
  by
  nth_rw 1 [← image_preimage_inl_union_image_preimage_inr I]
  rw [Sum, and_comm']
  simp only [congr.symm_indep_iff, direct_sum.indep_iff, Bool.forall_bool]
  convert Iff.rfl using 3 <;>
    · ext
      simp

@[simp]
theorem sum.base_iff {B : Set (Sum E₁ E₂)} :
    (sum M₁ M₂).base B ↔ M₁.base (Sum.inl ⁻¹' B) ∧ M₂.base (Sum.inr ⁻¹' B) :=
  by
  rw [Sum, and_comm']
  simp only [congr.symm_base_iff, Equiv.sumEquivSigmaBool_apply, direct_sum.base_iff,
    Bool.forall_bool]
  convert Iff.rfl using 3 <;>
    · ext
      simp

@[simp]
theorem sum.circuit_iff {C : Set (Sum E₁ E₂)} :
    (sum M₁ M₂).Circuit C ↔
      (∃ C₁, M₁.Circuit C₁ ∧ C = Sum.inl '' C₁) ∨ ∃ C₂, M₂.Circuit C₂ ∧ C = Sum.inr '' C₂ :=
  by
  rw [Sum, or_comm']
  simp only [congr.symm_circuit_iff, Equiv.sumEquivSigmaBool_apply, direct_sum.circuit_iff,
    Bool.exists_bool]
  convert Iff.rfl <;>-- squeeze_simp misbehaves in the line below.
    · ext
      convert Iff.rfl using 2
      simp_rw [Set.ext_iff]
      simp
      tauto

-- lemma sum.image_inl_union_image_inr_indep_iff {I₁ : set E₁} {I₂ : set E₂} :
--   (sum M₁ M₂).indep ((sum.inl '' I₁) ∪ (sum.inr '' I₂)) ↔ M₁.indep I₁ ∧ M₂.indep I₂ :=
-- by simp [preimage_image_eq _ sum.inl_injective, preimage_image_eq _ sum.inr_injective]
-- /-- Gluing together of an `ι`-indexed collection of different matroids on the same ground set.
--   This is a tamer special case of sigma, and is used in the proof of matroid union. -/
-- def copy_sum {E : Type*} (M : ι → matroid E) : matroid (ι × E) :=
--   (direct_sum M).congr_equiv (equiv.sigma_equiv_prod ι E)
-- @[simp] lemma copy_sum_base_iff {E : Type*} {M : ι → matroid E} {B : set (ι × E)}:
--   (copy_sum M).base B ↔ ∀ i, (M i).base (prod.mk i ⁻¹' B) :=
-- by {simp only [copy_sum, congr.apply_base, direct_sum_base_iff], congr'}
-- @[simp] lemma copy_sum_indep_iff {E : Type*} [finite ι] [finite E] {M : ι → matroid E}
-- {I : set (ι × E)}:
--   (copy_sum M).indep I ↔ ∀ i, (M i).indep (prod.mk i ⁻¹' I) :=
-- by {simp only [copy_sum, congr.apply_indep, direct_sum_indep_iff], congr'}
end Sum

section Partition

variable {ι : Type _} {E : ι → Type _} {rk : ι → ℕ} [Finite ι] [∀ i, Finite (E i)]

/-- The direct sum of uniform matroids with prescribed ranks -/
def partitionMatroid (E : ι → Type _) [∀ i, Finite (E i)] (rk : ι → ℕ) : Matroid (Σi, E i) :=
  directSum fun i => unifOn (E i) (rk i)

theorem partitionMatroid_base_iff (h_le : ∀ i, rk i ≤ Nat.card (E i)) {B : Set (Σi, E i)} :
    (partitionMatroid E rk).base B ↔ ∀ i, (Sigma.mk i ⁻¹' B).ncard = rk i :=
  by
  simp [partition_matroid]
  refine' ⟨fun h i => _, fun h i => _⟩
  · specialize h i
    rwa [unif_on_base_iff (h_le i), Sigma.ncard_preimage_mk] at h
  rw [unif_on_base_iff (h_le i), Sigma.ncard_preimage_mk]
  exact h i

@[simp]
theorem partitionMatroid_indep_iff {I : Set (Σi, E i)} :
    (partitionMatroid E rk).indep I ↔ ∀ i, (I ∩ fst ⁻¹' {i}).ncard ≤ rk i :=
  by
  simp only [partition_matroid, direct_sum.indep_iff, unif.indep_iff]
  refine' forall_congr' fun i => _
  rw [Sigma.ncard_preimage_mk]

@[simp]
theorem partitionMatroid_r_eq (X : Set (Σi, E i)) :
    (partitionMatroid E rk).R X = ∑ᶠ i, min (rk i) (X ∩ fst ⁻¹' {i}).ncard :=
  by
  simp only [partition_matroid, direct_sum.r_eq, unif_on_r]
  apply finsum_congr fun i => _
  rw [Sigma.ncard_preimage_mk]

theorem partition_one_flat_iff {F : Set (Σi, E i)} :
    (partitionMatroid E 1).Flat F ↔ ∀ i, fst ⁻¹' {i} ⊆ F ∨ Disjoint F (fst ⁻¹' {i}) :=
  by
  simp only [partition_matroid, Pi.one_apply, direct_sum.flat_iff, unif_on_flat_iff,
    ncard_preimage_mk, Nat.lt_one_iff, ncard_eq_zero]
  refine' forall_congr' fun i => _
  convert Iff.rfl
  · simp_rw [eq_univ_iff_forall, eq_iff_iff]
    exact
      ⟨fun h x => h (rfl : Sigma.fst ⟨i, x⟩ = i), fun h =>
        by
        rintro ⟨j, e⟩ (rfl : j = i)
        exact h _⟩
  simp_rw [eq_iff_iff, ← disjoint_iff_inter_eq_empty]

end Partition

section PartitionOn

variable {ι : Type} {E : Type v} [Finite E] [Finite ι] {f : E → ι} {rks : ι → ℕ}

/-- The partition matroid on ground set `E` induced by a partition `f : E → ι` of the ground set
  and ranks `rks : ι → ℕ`. -/
def partitionMatroidOn (f : E → ι) (rks : ι → ℕ) : Matroid E :=
  (partitionMatroid (fun i => { x // f x = i }) rks).congr (Equiv.sigmaFiberEquiv f)

@[simp]
theorem partitionMatroidOn_indep_iff {I : Set E} :
    (partitionMatroidOn f rks).indep I ↔ ∀ i, (I ∩ f ⁻¹' {i}).ncard ≤ rks i :=
  by
  -- rw [partition_matroid_on],
  simp only [partition_matroid_on, congr.indep_iff, partition_matroid_indep_iff]
  apply forall_congr' fun i => _
  rw [← ncard_image_of_injective _ (Equiv.sigmaFiberEquiv f).symm.Injective,
    image_inter (Equiv.sigmaFiberEquiv f).symm.Injective]
  convert Iff.rfl
  ext x
  obtain ⟨j, x, rfl⟩ := x
  simp only [mem_image, mem_preimage, mem_singleton_iff, Equiv.sigmaFiberEquiv,
    Equiv.coe_fn_symm_mk]
  constructor
  · rintro ⟨x', rfl, h⟩
    exact h.1.symm
  rintro rfl
  exact ⟨x, by simp⟩

@[simp]
theorem partitionMatroidOn_r_eq (X : Set E) :
    (partitionMatroidOn f rks).R X = ∑ᶠ i, min (rks i) (X ∩ f ⁻¹' {i}).ncard :=
  by
  simp only [partition_matroid_on, congr.r_eq, partition_matroid_r_eq]
  refine' finsum_congr fun i => _
  rw [← ncard_image_of_injective _ (Equiv.sigmaFiberEquiv f).symm.Injective, ←
    preimage_equiv_eq_image_symm, ← preimage_equiv_eq_image_symm, preimage_inter]
  convert rfl
  ext x
  obtain ⟨j, x, rfl⟩ := x
  simp

theorem partitionMatroidOn_one_r_eq (X : Set E) : (partitionMatroidOn f 1).R X = (f '' X).ncard :=
  by
  simp only [partition_matroid_on_r_eq, Pi.one_apply]
  rw [← finsum_mem_one]
  apply finsum_congr fun i => _
  rw [finsum_eq_if, min_one_ncard_eq_ite (to_finite (X ∩ f ⁻¹' {i}))]
  convert rfl

end PartitionOn

end Matroid

