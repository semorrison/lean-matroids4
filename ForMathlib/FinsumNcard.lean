import Mathlib.Algebra.BigOperators.Finprod
import Project.Mathlib.Data.Set.Basic
import Project.Mathlib.Data.Set.Sigma
import Project.Mathlib.Ncard
import Mathlib.Data.Setoid.Partition

noncomputable section

open BigOperators Classical

/-!
A few helper lemmas for a separate PR
-/


open Set

section Sigma

variable {ι : Type _} {α : ι → Type _} [Finite ι] {x y : Set (Σi, α i)} {f : ∀ i, Set (α i)}
  {i j : ι}

@[simp]
theorem finsum_mem_one {α : Type _} (s : Set α) : (∑ᶠ a ∈ s, 1) = s.ncard :=
  by
  have hsupp := @Function.support_const α _ _ _ Nat.one_ne_zero
  obtain h | h := s.finite_or_infinite
  · have h' := h
    rw [← inter_univ s, ← hsupp] at h'
    convert finsum_mem_eq_sum _ h'
    rw [← Finset.card_eq_sum_ones, ncard_eq_to_finset_card _ h]
    congr
    rw [hsupp, inter_univ]
  rw [h.ncard, finsum_mem_eq_zero_of_infinite]
  rwa [hsupp, inter_univ]

@[simp]
theorem finsum_one (α : Sort _) : (∑ᶠ a : α, 1) = Nat.card α := by
  rw [← finsum_mem_univ, finsum_mem_one, ncard_univ]

theorem Sigma.ncard_eq_finsum_ncard_image_preimage_mk (x : Set (Σi, α i)) (hx : x.Finite) :
    x.ncard = ∑ᶠ i, (Sigma.mk i '' (Sigma.mk i ⁻¹' x)).ncard :=
  by
  rw [← finsum_mem_one, Sigma.eq_iUnion_image_preimage_mk x,
    finsum_mem_iUnion (Sigma.image_preimage_mk_pairwise_disjoint x)]
  · simp [← finsum_mem_one]
  exact fun i => hx.subset (by simp)

theorem min_one_ncard_eq_ite {α : Type _} {s : Set α} (hs : s.Finite) :
    min 1 s.ncard = ite s.Nonempty 1 0 :=
  by
  obtain rfl | h := s.eq_empty_or_nonempty; simp
  rwa [if_pos h, min_eq_left_iff, Nat.add_one_le_iff, ncard_pos hs]

@[simp]
theorem Sigma.ncard_preimage_mk (x : Set (Σi, α i)) (i : ι) :
    (Sigma.mk i ⁻¹' x).ncard = (x ∩ Sigma.fst ⁻¹' {i}).ncard :=
  by
  rw [← range_sigma_mk, ← preimage_inter_range,
    ncard_preimage_of_injective_subset_range sigma_mk_injective]
  apply inter_subset_right

end Sigma

section finsum

theorem finsum_mem_le_finsum_mem {ι N : Type _} [OrderedAddCommMonoid N] {f g : ι → N} {s : Set ι}
    (hf : (s ∩ Function.support f).Finite) (hg : (s ∩ Function.support g).Finite)
    (h : ∀ i : ι, i ∈ s → f i ≤ g i) : (∑ᶠ i ∈ s, f i) ≤ ∑ᶠ i ∈ s, g i :=
  by
  set hs' := hf.union hg
  rw [← inter_distrib_left] at hs'
  rw [@finsum_mem_eq_sum_of_inter_support_eq _ _ _ f _ hs'.to_finset,
    @finsum_mem_eq_sum_of_inter_support_eq _ _ _ g _ hs'.to_finset]
  · apply Finset.sum_le_sum
    simp only [finite.mem_to_finset, mem_inter_iff, mem_union, Function.mem_support, and_imp]
    exact fun i hi h' => h i hi
  · rw [finite.coe_to_finset, inter_assoc, inter_eq_self_of_subset_right (subset_union_right _ _)]
  rw [finite.coe_to_finset, inter_assoc, inter_eq_self_of_subset_right (subset_union_left _ _)]

theorem finsum_le_finsum {ι N : Type _} [OrderedAddCommMonoid N] {f g : ι → N}
    (hf : f.support.Finite) (hg : g.support.Finite) (h : ∀ i, f i ≤ g i) :
    (∑ᶠ i, f i) ≤ ∑ᶠ i, g i := by
  rw [← finsum_mem_univ]
  nth_rw 2 [← finsum_mem_univ]
  apply finsum_mem_le_finsum_mem <;> simpa

/-- If `f ≤ g` pointwise on `s`, but the sum of `g` is at most the sum of `f`, then `f = g` on `s`-/
theorem eq_of_finsum_mem_ge_finsum_mem_of_forall_le {ι N : Type _} [OrderedCancelAddCommMonoid N]
    {f g : ι → N} {s : Set ι} (hf : (s ∩ f.support).Finite) (hg : (s ∩ g.support).Finite)
    (h_le : ∀ i ∈ s, f i ≤ g i) (h_ge : (∑ᶠ i ∈ s, g i) ≤ ∑ᶠ i ∈ s, f i) {a : ι} (ha : a ∈ s) :
    f a = g a := by
  refine' (h_le a ha).antisymm _
  set s' := s \ {a} with hs'
  have hs'f : (s \ {a} ∩ f.support).Finite :=
    hf.subset (inter_subset_inter_left _ (diff_subset _ _))
  have hs'g : (s \ {a} ∩ g.support).Finite :=
    hg.subset (inter_subset_inter_left _ (diff_subset _ _))
  rw [← insert_eq_of_mem ha, ← insert_diff_singleton,
    finsum_mem_insert' _ (not_mem_diff_singleton _ _) hs'f,
    finsum_mem_insert' _ (not_mem_diff_singleton _ _) hs'g] at h_ge
  exact
    le_of_add_le_add_right
      ((add_le_add_left (finsum_mem_le_finsum_mem hs'f hs'g fun i hi => h_le _ hi.1) (g a)).trans
        h_ge)

theorem eq_of_finsum_ge_finsum_of_forall_le {ι N : Type _} [OrderedCancelAddCommMonoid N]
    {f g : ι → N} (hf : f.support.Finite) (hg : g.support.Finite) (h_le : ∀ i, f i ≤ g i)
    (h_ge : (∑ᶠ i, g i) ≤ ∑ᶠ i, f i) (a : ι) : f a = g a :=
  by
  rw [← finsum_mem_univ f, ← finsum_mem_univ g] at h_ge
  exact
    eq_of_finsum_mem_ge_finsum_mem_of_forall_le (by rwa [univ_inter]) (by rwa [univ_inter])
      (fun i _ => h_le i) h_ge (mem_univ a)

theorem finsum_le_finsum_of_subset {ι M : Type _} [CanonicallyOrderedAddMonoid M] {f : ι → M}
    {s t : Set ι} (h : s ⊆ t) (ht : t.Finite) : (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ t, f x :=
  by
  rw [← inter_union_diff t s, inter_eq_right_iff_subset.mpr h,
    finsum_mem_union (@disjoint_sdiff_self_right _ s t _) (ht.subset h) (ht.diff _)]
  exact le_add_right rfl.le

theorem finsum_le_finsum_of_subset' {ι M : Type _} [CanonicallyOrderedAddMonoid M] {f : ι → M}
    {s t : Set ι} (h : s ⊆ t) (ht : (t ∩ f.support).Finite) : (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ t, f x :=
  by
  rw [← finsum_mem_inter_support]
  nth_rw 2 [← finsum_mem_inter_support]
  apply finsum_le_finsum_of_subset (inter_subset_inter_left _ h) ht

theorem mem_le_finsum {ι M : Type _} [CanonicallyOrderedAddMonoid M] {f : ι → M} {x : ι} {t : Set ι}
    (h : x ∈ t) (ht : t.Finite) : f x ≤ ∑ᶠ x ∈ t, f x :=
  by
  rw [← @finsum_mem_singleton _ _ _ f x]
  exact finsum_le_finsum_of_subset (singleton_subset_iff.mpr h) ht

theorem mem_le_finsum' {ι M : Type _} [CanonicallyOrderedAddMonoid M] {f : ι → M} {x : ι}
    {t : Set ι} (h : x ∈ t) (ht : (t ∩ f.support).Finite) : f x ≤ ∑ᶠ x ∈ t, f x :=
  by
  rw [← @finsum_mem_singleton _ _ _ f x]
  exact finsum_le_finsum_of_subset' (singleton_subset_iff.mpr h) ht

theorem ncard_sUnion_le {α : Type _} (s : Set (Set α)) (hs : s.Finite)
    (hs' : ∀ x ∈ s, Set.Finite x) : (⋃₀ s).ncard ≤ ∑ᶠ x ∈ s, ncard x :=
  by
  refine' Set.Finite.induction_on hs (by simp) fun a t hat ht h => _
  rw [sUnion_insert, finsum_mem_insert _ hat ht]
  exact (ncard_union_le _ _).trans (add_le_add rfl.le h)

theorem ncard_iUnion_le {ι α : Type _} [Finite ι] (s : ι → Set α) (h : ∀ i, (s i).Finite) :
    (⋃ i, s i).ncard ≤ ∑ᶠ i, (s i).ncard :=
  by
  suffices h' : ∀ t : Set ι, (⋃ i ∈ t, s i).ncard ≤ ∑ᶠ i ∈ t, (s i).ncard
  · convert h' univ <;> simp
  refine' fun t => (to_finite t).inductionOn (by simp) _
  intro a t₀ hat₀ ht₀ IH
  rw [bUnion_insert, finsum_mem_insert _ hat₀ ht₀]
  exact (ncard_union_le _ _).trans (add_le_add rfl.le IH)

@[simp]
theorem finsum_mem_boole {α : Type _} (s : Set α) (p : α → Prop) :
    (∑ᶠ x ∈ s, ite (p x) 1 0) = (s ∩ setOf p).ncard :=
  by
  have hsupp : s ∩ setOf p = s ∩ Function.support fun x => ite (p x) 1 0 :=
    by
    ext
    simp
  cases (s ∩ setOf p).finite_or_infinite
  · have h' : (s ∩ Function.support fun x => ite (p x) 1 0).Finite := by rwa [← hsupp]
    rw [finsum_mem_eq_sum _ h', ncard_eq_to_finset_card _ h]
    simp only [Finset.sum_boole, Finset.filter_true_of_mem, finite.mem_to_finset, mem_inter_iff,
      Function.mem_support, Ne.def, ite_eq_right_iff, Nat.one_ne_zero, not_forall, not_false_iff,
      exists_prop, and_true_iff, and_imp, imp_self, imp_true_iff, Nat.cast_id]
    convert rfl
  rw [finsum_mem_eq_zero_of_infinite, h.ncard]
  rwa [← hsupp]

@[simp]
theorem finsum_boole {α : Type _} (p : α → Prop) : (∑ᶠ x, ite (p x) 1 0) = (setOf p).ncard := by
  rw [← finsum_mem_univ, finsum_mem_boole, univ_inter]

theorem ncard_eq_finsum_fiber {α ι : Type _} {s : Set α} (hs : s.Finite) (f : α → ι) :
    s.ncard = ∑ᶠ i : ι, (s ∩ f ⁻¹' {i}).ncard :=
  by
  have h' : (Function.support fun i => (s ∩ f ⁻¹' {i}).ncard).Finite :=
    by
    apply (hs.image f).Subset
    rintro i (h : ¬_ = 0)
    rw [ncard_eq_zero (hs.subset (inter_subset_left _ _)), ← Ne.def, ← nonempty_iff_ne_empty] at h
    obtain ⟨x, hxs, hx⟩ := h
    exact ⟨x, hxs, by simpa using hx⟩
  rw [ncard_eq_to_finset_card _ hs,
    @Finset.card_eq_sum_card_fiberwise _ _ _ f hs.to_finset (hs.image f).toFinset]
  · rw [← finsum_mem_univ, ← finsum_mem_inter_support, univ_inter,
      finsum_mem_eq_finite_toFinset_sum _ h', Finset.sum_congr]
    · ext
      simp_rw [finite.mem_to_finset, mem_image, Function.mem_support, Ne.def,
        ncard_eq_zero (hs.subset (inter_subset_left _ _)), eq_empty_iff_forall_not_mem, not_forall,
        mem_inter_iff, Classical.not_not, mem_preimage, mem_singleton_iff]
    intro x hx
    rw [ncard_eq_to_finset_card _ (hs.subset (inter_subset_left _ _))]
    convert rfl
    ext
    simp
  simp only [finite.mem_to_finset, mem_image]
  exact fun x hx => ⟨x, hx, rfl⟩

theorem card_eq_finsum_fiber {α ι : Type _} [Finite α] (f : α → ι) :
    Nat.card α = ∑ᶠ i : ι, (f ⁻¹' {i}).ncard :=
  by
  rw [← ncard_univ]
  convert ncard_eq_finsum_fiber (to_finite univ) f using 1
  exact finsum_congr fun _ => by rw [univ_inter]

theorem finsum_indexedPartition_ncard_eq {α ι : Type _} [Finite α] {s : ι → Set α}
    (h : IndexedPartition s) : (∑ᶠ i, Set.ncard (s i)) = Nat.card α :=
  by
  simp_rw [h.eq]
  convert(card_eq_finsum_fiber h.index).symm

/-- A `setoid` partition noncomputably gives rise to an indexed partition -/
noncomputable def Setoid.IsPartition.indexedPartition {α : Type _} {c : Set (Set α)}
    (h : Setoid.IsPartition c) : @IndexedPartition c α coe :=
  IndexedPartition.mk' coe
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hne
      exact h.pairwise_disjoint ha hb (by simpa using hne))
    (by
      rintro ⟨a, ha⟩
      exact Setoid.nonempty_of_mem_partition h ha)
    (by
      intro x
      have hu := mem_univ x
      rw [← h.sUnion_eq_univ, mem_sUnion] at hu
      obtain ⟨t, htc, htx⟩ := hu
      exact ⟨⟨t, htc⟩, htx⟩)

theorem finsum_partition_eq {α : Type _} [Finite α] {c : Set (Set α)} (h : Setoid.IsPartition c) :
    (∑ᶠ s ∈ c, Set.ncard s) = Nat.card α :=
  by
  convert finsum_indexedPartition_ncard_eq h.indexed_partition using 1
  rw [finsum_set_coe_eq_finsum_mem]

end finsum

