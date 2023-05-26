import Matroid.Circuit
import Project.Mathlib.Data.Set.Basic
import Project.Mathlib.FinsumNcard

noncomputable section

open Classical

open BigOperators

variable {E : Type _} {M M₁ M₂ : Matroid E} {I B C X Y Z K F F₀ F₁ F₂ H H₁ H₂ : Set E}
  {e f x y z : E}

open Set

namespace Matroid

theorem flat_def : M.Flat F ↔ ∀ I X, M.Basis I F → M.Basis I X → X ⊆ F :=
  Iff.rfl

theorem Flat.iInter {ι : Type _} (F : ι → Set E) (hF : ∀ i, M.Flat (F i)) : M.Flat (⋂ i, F i) :=
  by
  refine' fun I X hI hIX => subset_Inter fun i => _
  obtain ⟨J, hIJ, hJ⟩ :=
    hI.indep.subset_basis_of_subset (hI.subset.trans (Inter_subset _ _) : I ⊆ F i)
  refine' (union_subset_iff.mp (@hF i _ (F i ∪ X) hIJ _)).2
  rw [← union_eq_left_iff_subset.mpr hIJ.subset, union_assoc]
  exact hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ)

theorem flat_of_cl (M : Matroid E) (X : Set E) : M.Flat (M.cl X) :=
  by
  rw [cl_def, sInter_eq_Inter]
  refine' flat.Inter _ _
  rintro ⟨F, hF⟩
  exact hF.1

theorem flat_iff_cl_self : M.Flat F ↔ M.cl F = F :=
  ⟨fun h => subset_antisymm (sInter_subset_of_mem ⟨h, Subset.rfl⟩) (M.subset_cl _), fun h =>
    by
    rw [← h]
    exact flat_of_cl _ _⟩

theorem Flat.cl (hF : M.Flat F) : M.cl F = F :=
  flat_iff_cl_self.mp hF

theorem Flat.inter (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.Flat (F₁ ∩ F₂) :=
  by
  rw [inter_eq_Inter]
  refine' flat.Inter _ fun i => _
  cases i <;> assumption

@[simp]
theorem univ_flat (M : Matroid E) : M.Flat univ :=
  by
  convert@flat.Inter _ M Empty Empty.elim fun i => Empty.elim i
  simp

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e «expr ∉ » F) -/
theorem flat_iff_sSubset_cl_insert_forall :
    M.Flat F ↔ ∀ (e) (_ : e ∉ F), M.cl F ⊂ M.cl (insert e F) :=
  by
  refine' ⟨fun h e he => (M.cl_subset (subset_insert _ _)).ssubset_of_ne _, fun h => _⟩
  · rw [h.cl]
    exact fun h' => mt ((set.ext_iff.mp h') e).mpr he ((M.subset_cl _) (mem_insert _ _))
  rw [flat_iff_cl_self]
  by_contra h'
  obtain ⟨e, he', heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (Ne.symm h') (M.subset_cl F))
  have h'' := h e heF
  rw [← cl_insert_cl_eq_cl_insert, insert_eq_of_mem he', cl_cl] at h''
  exact h''.ne rfl

theorem flat_iff_forall_circuit {F : Set E} :
    M.Flat F ↔ ∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F :=
  by
  rw [flat_iff_cl_self]
  refine'
    ⟨fun h C e hC heC hCF => _, fun h =>
      (M.subset_cl _).antisymm' fun e heF => by_contra fun he' => _⟩
  · rw [← h]
    refine' (M.cl_subset _) (hC.subset_cl_diff_singleton e heC)
    rwa [diff_subset_iff, singleton_union]
  obtain ⟨C, hC, heC, hCF⟩ := (mem_cl_iff_exists_circuit_of_not_mem he').mp heF
  exact he' (h C e hC heC hCF)

theorem Flat.cl_exchange (hF : M.Flat F) (he : e ∈ M.cl (insert f F) \ F) :
    f ∈ M.cl (insert e F) \ F := by
  nth_rw 2 [← hF.cl]
  apply cl_exchange
  rwa [hF.cl]

theorem Flat.cl_insert_eq_cl_insert_of_mem (hF : M.Flat F) (he : e ∈ M.cl (insert f F) \ F) :
    M.cl (insert e F) = M.cl (insert f F) :=
  by
  apply cl_insert_eq_cl_insert_of_mem
  rwa [hF.cl]

theorem Flat.cl_subset_of_subset (hF : M.Flat F) (h : X ⊆ F) : M.cl X ⊆ F :=
  by
  have h' := M.cl_mono h
  rwa [hF.cl] at h'

-- ### Covering
/-- A flat is covered by another in a matroid if they are strictly nested, with no flat
  between them . -/
def Covby (M : Matroid E) (F₀ F₁ : Set E) : Prop :=
  M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁

theorem covby_iff :
    M.Covby F₀ F₁ ↔
      M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ :=
  Iff.rfl

theorem Covby.flat_left (h : M.Covby F₀ F₁) : M.Flat F₀ :=
  h.1

theorem Covby.flat_right (h : M.Covby F₀ F₁) : M.Flat F₁ :=
  h.2.1

theorem Covby.sSubset (h : M.Covby F₀ F₁) : F₀ ⊂ F₁ :=
  h.2.2.1

theorem Covby.subset (h : M.Covby F₀ F₁) : F₀ ⊆ F₁ :=
  h.2.2.1.Subset

theorem Covby.eq_or_eq (h : M.Covby F₀ F₁) (hF : M.Flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
    F = F₀ ∨ F = F₁ :=
  h.2.2.2 F hF h₀ h₁

theorem Covby.eq_of_subset_of_sSubset (h : M.Covby F₀ F₁) (hF : M.Flat F) (hF₀ : F₀ ⊆ F)
    (hF₁ : F ⊂ F₁) : F = F₀ :=
  (h.2.2.2 F hF hF₀ hF₁.Subset).elim id fun h' => (hF₁.Ne h').elim

theorem Covby.eq_of_sSubset_of_subset (h : M.Covby F₀ F₁) (hF : M.Flat F) (hF₀ : F₀ ⊂ F)
    (hF₁ : F ⊆ F₁) : F = F₁ :=
  (h.2.2.2 F hF hF₀.Subset hF₁).elim (fun h' => (hF₀.Ne.symm h').elim) id

theorem Covby.cl_insert_eq (h : M.Covby F₀ F₁) (he : e ∈ F₁ \ F₀) : M.cl (insert e F₀) = F₁ :=
  h.eq_of_sSubset_of_subset (M.flat_of_cl _) ((ssubset_insert he.2).trans_subset (M.subset_cl _))
    (h.flat_right.cl_subset_of_subset (insert_subset.mpr ⟨he.1, h.SSubset.Subset⟩))

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e «expr ∉ » F₀) -/
theorem Flat.covby_iff_eq_cl_insert (hF₀ : M.Flat F₀) :
    M.Covby F₀ F₁ ↔ ∃ (e : _)(_ : e ∉ F₀), F₁ = M.cl (insert e F₀) :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨e, heF₁, heF₀⟩ := exists_of_ssubset h.ssubset
    simp_rw [← h.cl_insert_eq ⟨heF₁, heF₀⟩]
    exact ⟨_, heF₀, rfl⟩
  rintro ⟨e, heF₀, rfl⟩
  refine'
    ⟨hF₀, M.flat_of_cl _, (M.subset_cl_of_subset (subset_insert _ _)).sSubset_of_nonempty_diff _,
      fun F hF hF₀F hFF₁ => _⟩
  · exact ⟨e, M.mem_cl_of_mem (mem_insert _ _), heF₀⟩
  refine'
    or_iff_not_imp_left.mpr fun hne =>
      hFF₁.antisymm (hF.cl_subset_of_subset (insert_subset.mpr ⟨_, hF₀F⟩))
  obtain ⟨f, hfF, hfF₀⟩ := exists_of_ssubset (hF₀F.ssubset_of_ne (Ne.symm hne))
  obtain ⟨he', -⟩ := hF₀.cl_exchange ⟨hFF₁ hfF, hfF₀⟩
  exact mem_of_mem_of_subset he' (hF.cl_subset_of_subset (insert_subset.mpr ⟨hfF, hF₀F⟩))

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e «expr ∉ » M.cl X) -/
theorem cl_covby_iff : M.Covby (M.cl X) F ↔ ∃ (e : _)(_ : e ∉ M.cl X), F = M.cl (insert e X) := by
  simp_rw [(M.flat_of_cl X).covby_iff_eq_cl_insert, cl_insert_cl_eq_cl_insert]

theorem Flat.existsUnique_flat_of_not_mem (hF₀ : M.Flat F₀) (he : e ∉ F₀) :
    ∃! F₁, e ∈ F₁ ∧ M.Covby F₀ F₁ :=
  by
  simp_rw [hF₀.covby_iff_eq_cl_insert]
  refine' ⟨M.cl (insert e F₀), ⟨M.mem_cl_of_mem (mem_insert _ _), ⟨e, he, rfl⟩⟩, _⟩
  simp only [exists_prop, and_imp, forall_exists_index]
  rintro X heX f hfF₀ rfl
  rw [hF₀.cl_insert_eq_cl_insert_of_mem ⟨heX, he⟩]

theorem Flat.covby_partition (hF : M.Flat F) :
    Setoid.IsPartition (insert F ((fun F₁ => F₁ \ F) '' { F₁ | M.Covby F F₁ }) \ {∅}) :=
  by
  refine' ⟨not_mem_diff_singleton _ _, fun e => (em (e ∈ F)).elim (fun heF => ⟨F, _⟩) fun heF => _⟩
  · simp only [mem_diff, mem_insert_iff, eq_self_iff_true, mem_image, mem_set_of_eq, true_or_iff,
      mem_singleton_iff, true_and_iff, exists_unique_iff_exists, exists_prop, and_imp,
      forall_eq_or_imp, imp_true_iff, forall_exists_index, forall_apply_eq_imp_iff₂]
    simp_rw [iff_true_intro heF, and_true_iff, not_true, false_imp_iff, imp_true_iff, and_true_iff]
    rintro rfl
    exact not_mem_empty e heF
  · simp only [mem_diff, mem_insert_iff, mem_image, mem_set_of_eq, mem_singleton_iff,
      exists_unique_iff_exists, exists_prop]
    obtain ⟨F', hF'⟩ := hF.exists_unique_flat_of_not_mem heF
    simp only [and_imp] at hF'
    use F' \ F
    simp only [and_imp, forall_eq_or_imp, forall_exists_index, forall_apply_eq_imp_iff₂, mem_diff,
      iff_false_intro heF, IsEmpty.forall_iff, imp_true_iff, not_false_iff, forall_true_left,
      true_and_iff, ← Ne.def, ← nonempty_iff_ne_empty, and_true_iff]
    refine' ⟨⟨⟨Or.inr ⟨_, hF'.1.2, rfl⟩, ⟨e, hF'.1.1, heF⟩⟩, hF'.1.1⟩, fun F₁ hFF₁ hne heF₁ => _⟩
    rw [hF'.2 F₁ heF₁ hFF₁]

theorem Flat.covby_partition_of_nonempty (hF : M.Flat F) (hFne : F.Nonempty) :
    Setoid.IsPartition (insert F ((fun F₁ => F₁ \ F) '' { F₁ | M.Covby F F₁ })) :=
  by
  convert hF.covby_partition
  rw [eq_comm, sdiff_eq_left, disjoint_singleton_right]
  rintro (rfl | ⟨F', hF', h⟩)
  · exact not_nonempty_empty hFne
  refine' hF'.ssubset.not_subset _
  simpa [diff_eq_empty] using h

theorem Flat.covby_partition_of_empty (hF : M.Flat ∅) : Setoid.IsPartition { F | M.Covby ∅ F } :=
  by
  convert hF.covby_partition
  simp only [diff_empty, image_id', insert_diff_of_mem, mem_singleton, setOf]
  ext F
  simp_rw [mem_diff, mem_singleton_iff, iff_self_and]
  rintro hF' rfl
  exact hF'.ssubset.ne rfl

theorem Flat.sum_ncard_diff_of_covby [Finite E] (hF : M.Flat F) :
    (F.ncard + ∑ᶠ F' ∈ { F' | M.Covby F F' }, (F' \ F).ncard) = Nat.card E :=
  by
  obtain rfl | hFne := F.eq_empty_or_nonempty
  · convert finsum_partition_eq hF.covby_partition_of_empty
    simp
  convert finsum_partition_eq (hF.covby_partition_of_nonempty hFne)
  rw [finsum_mem_insert, add_left_cancel_iff, finsum_mem_image]
  · rintro F₁ hF₁ F₂ hF₂ (h : F₁ \ F = F₂ \ F)
    rw [← diff_union_of_subset hF₁.subset, h, diff_union_of_subset hF₂.subset]
  · rintro ⟨F', hF', h : F' \ F = F⟩
    obtain ⟨e, he⟩ := hFne
    exact (h.symm.subset he).2 he
  exact (to_finite _).image _

theorem Flat.cl_eq_iff_basis_of_indep (hF : M.Flat F) (hI : M.indep I) : M.cl I = F ↔ M.Basis I F :=
  ⟨by
    rintro rfl
    exact hI.basis_cl, fun h => by rw [h.cl, hF.cl]⟩

-- ### Hyperplanes
section Hyperplane

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (B «expr ⊆ » X) -/
/-- A hyperplane is a maximal set containing no base  -/
def Hyperplane (M : Matroid E) (H : Set E) : Prop :=
  H ∈ maximals (· ⊆ ·) { X | ¬∃ (B : _)(_ : B ⊆ X), M.base B }

theorem Hyperplane.cl_eq_univ_of_ssupset (hH : M.Hyperplane H) (hX : H ⊂ X) : M.cl X = univ :=
  base_subset_iff_cl_eq_univ.mp (by_contra fun h => hX.not_subset (hH.2 h hX.Subset))

theorem Hyperplane.flat (hH : M.Hyperplane H) : M.Flat H :=
  by
  refine' fun I X hIH hIX e heX =>
    hH.2 (fun h' => hH.1 ⟨I, hIH.Subset, _⟩) (subset_insert e H) (mem_insert e H)
  obtain ⟨B, hBeH, hB⟩ := h'
  exact
    (hIH.basis_union hIX).base_of_base_subset hB
      (hBeH.trans (insert_subset.mpr ⟨Or.inr heX, subset_union_left _ _⟩))

theorem Hyperplane.sSubset_univ (hH : M.Hyperplane H) : H ⊂ univ :=
  ssubset_univ_iff.mpr
    (by
      rintro rfl
      exact hH.1 (M.exists_base.imp fun B hB => ⟨subset_univ B, hB⟩))

theorem Hyperplane.flat_supset_eq_univ (hH : M.Hyperplane H) (hF : M.Flat F) (hHF : H ⊂ F) :
    F = univ := by rw [← hF.cl, hH.cl_eq_univ_of_ssupset hHF]

theorem hyperplane_iff_maximal_proper_flat :
    M.Hyperplane H ↔ M.Flat H ∧ H ⊂ univ ∧ ∀ F, H ⊂ F → M.Flat F → F = univ :=
  by
  refine'
    ⟨fun h => ⟨h.Flat, h.sSubset_univ, fun F hHF hF => h.flat_supset_eq_univ hF hHF⟩, fun h =>
      ⟨_, fun X hX hHX => hHX.eq_or_ssubset.elim (fun h' => h'.symm.subset) fun hss => (hX _).elim⟩⟩
  · rintro ⟨B, hBH, hB⟩
    have hcl := M.cl_subset hBH
    rw [hB.cl, univ_subset_iff, h.1.cl] at hcl
    exact h.2.1.Ne hcl
  have hX_univ := h.2.2 _ (hss.trans_subset (M.subset_cl X)) (M.flat_of_cl _)
  rwa [← base_subset_iff_cl_eq_univ] at hX_univ

@[simp]
theorem compl_cocircuit_iff_hyperplane : M.Cocircuit (Hᶜ) ↔ M.Hyperplane H :=
  by
  simp_rw [hyperplane, cocircuit, circuit, indep_iff_subset_base, dual.base_iff]
  refine'
    ⟨fun h => ⟨fun h' => h.1 (Exists.imp' compl (fun B hB => _) h'), fun X hX hXH => _⟩, fun h =>
      ⟨fun h' => h.1 (Exists.imp' compl (fun B hB => _) h'), fun X hX hXH => _⟩⟩
  · rwa [compl_subset_compl, compl_compl, and_comm', ← exists_prop]
  · refine' compl_subset_compl.mp (h.2 _ (compl_subset_compl.mpr hXH))
    exact fun ⟨B, hBX, hB⟩ => hX ⟨Bᶜ, compl_subset_comm.mp hB, hBX⟩
  · rwa [exists_prop, and_comm', compl_subset_comm]
  refine' compl_subset_comm.mp (h.2 _ (subset_compl_comm.mp hXH))
  exact fun ⟨B, hBX, hB⟩ => hX ⟨Bᶜ, by rwa [compl_compl], by rwa [subset_compl_comm]⟩

@[simp]
theorem compl_hyperplane_iff_cocircuit : M.Hyperplane (Kᶜ) ↔ M.Cocircuit K := by
  rw [← compl_cocircuit_iff_hyperplane, compl_compl]

theorem Hyperplane.compl_cocircuit (hH : M.Hyperplane H) : M.Cocircuit (Hᶜ) :=
  compl_cocircuit_iff_hyperplane.mpr hH

theorem Cocircuit.compl_hyperplane {K : Set E} (hK : M.Cocircuit K) : M.Hyperplane (Kᶜ) :=
  compl_hyperplane_iff_cocircuit.mpr hK

theorem univ_not_hyperplane (M : Matroid E) : ¬M.Hyperplane univ := fun h => h.sSubset_univ.Ne rfl

theorem Hyperplane.eq_of_subset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) (h : H₁ ⊆ H₂) :
    H₁ = H₂ :=
  h.antisymm (h₁.2 h₂.1 h)

theorem Hyperplane.not_sSubset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) : ¬H₁ ⊂ H₂ :=
  fun hss => hss.Ne (h₁.eq_of_subset h₂ hss.Subset)

theorem Hyperplane.exists_not_mem (hH : M.Hyperplane H) : ∃ e, e ∉ H :=
  by
  by_contra' h
  apply M.univ_not_hyperplane
  convert hH
  rwa [eq_comm, eq_univ_iff_forall]

theorem hyperplane_iff_maximal_cl_ne_univ :
    M.Hyperplane H ↔ M.cl H ≠ univ ∧ ∀ X, H ⊂ X → M.cl X = univ :=
  by
  simp_rw [Ne.def, ← base_subset_iff_cl_eq_univ, hyperplane, maximals, mem_set_of]
  exact
    ⟨fun h => ⟨h.1, fun X h' => by_contra fun hex => h'.not_subset (h.2 hex h'.Subset)⟩, fun h =>
      ⟨h.1, fun X hex h' =>
        h'.eq_or_ssubset.elim (Eq.subset ∘ Eq.symm) fun hss => (hex (h.2 _ hss)).elim⟩⟩

theorem Base.hyperplane_of_cl_diff_singleton (hB : M.base B) (heB : e ∈ B) :
    M.Hyperplane (M.cl (B \ {e})) :=
  by
  rw [hyperplane_iff_maximal_cl_ne_univ, cl_cl, ne_univ_iff_exists_not_mem]
  refine'
    ⟨⟨e, fun he => indep_iff_cl_diff_ne_forall.mp hB.indep _ heB (cl_diff_singleton_eq_cl he)⟩,
      fun X hX => univ_subset_iff.mp _⟩
  obtain ⟨f, hfX, hfB⟩ := exists_of_ssubset hX
  obtain rfl | hef := eq_or_ne f e
  · have hu := union_subset (singleton_subset_iff.mpr hfX) ((subset_cl _ _).trans hX.subset)
    rw [singleton_union, insert_diff_singleton, insert_eq_of_mem heB] at hu
    exact hB.cl.symm.trans_subset (M.cl_subset hu)
  rw [(hB.indep.diff {e}).not_mem_cl_iff] at hfB
  have hf : f ∉ B := by
    refine' fun hf => hef _
    simp only [mem_diff, mem_singleton_iff, not_and, Classical.not_not] at hfB
    exact hfB.1 hf
  rw [← (hB.exchange_base_of_indep heB hf hfB.2).cl]
  exact M.cl_subset (insert_subset.mpr ⟨hfX, subset_trans (M.subset_cl _) hX.subset⟩)

theorem Hyperplane.ssupset_eq_univ_of_flat (hH : M.Hyperplane H) (hF : M.Flat F) (h : H ⊂ F) :
    F = univ := by
  rw [hyperplane_iff_maximal_cl_ne_univ] at hH
  rw [← hH.2 F h, hF.cl]

theorem Hyperplane.cl_insert_eq_univ (hH : M.Hyperplane H) (he : e ∉ H) :
    M.cl (insert e H) = univ :=
  hH.ssupset_eq_univ_of_flat (M.flat_of_cl _) ((ssubset_insert he).trans_subset (M.subset_cl _))

theorem exists_hyperplane_sep_of_not_mem_cl (h : e ∉ M.cl X) :
    ∃ H, M.Hyperplane H ∧ X ⊆ H ∧ e ∉ H :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.cl, hI.indep.not_mem_cl_iff] at h
  obtain ⟨B, hB, heIB⟩ := h.2.exists_base_supset
  rw [insert_subset] at heIB
  refine' ⟨M.cl (B \ {e}), hB.hyperplane_of_cl_diff_singleton heIB.1, _, fun hecl => _⟩
  · exact hI.subset_cl.trans (M.cl_subset (subset_diff_singleton heIB.2 h.1))
  exact indep_iff_cl_diff_ne_forall.mp hB.indep e heIB.1 (cl_diff_singleton_eq_cl hecl)

theorem cl_eq_sInter_hyperplanes (M : Matroid E) (X : Set E) :
    M.cl X = ⋂₀ { H | M.Hyperplane H ∧ X ⊆ H } :=
  by
  apply subset_antisymm
  · simp only [subset_sInter_iff, mem_set_of_eq, and_imp]
    exact fun H hH hXH => hH.flat.cl_subset_of_subset hXH
  by_contra' h'
  obtain ⟨x, h, hx⟩ := not_subset.mp h'
  obtain ⟨H, hH, hXH, hxH⟩ := exists_hyperplane_sep_of_not_mem_cl hx
  exact hxH (h H ⟨hH, hXH⟩)

theorem mem_cl_iff_forall_hyperplane : e ∈ M.cl X ↔ ∀ H, M.Hyperplane H → X ⊆ H → e ∈ H := by
  simp [cl_eq_sInter_hyperplanes]

theorem mem_dual_cl_iff_forall_circuit :
    e ∈ M﹡.cl X ↔ ∀ C, M.Circuit C → e ∈ C → (X ∩ C).Nonempty :=
  by
  rw [← dual_dual M]
  simp_rw [dual_circuit_iff_cocircuit, ← compl_hyperplane_iff_cocircuit, dual_dual,
    mem_cl_iff_forall_hyperplane]
  refine' ⟨fun h K hH heK => _, fun h H hH hXH => by_contra fun heH => _⟩
  · have h' := h _ hH
    rwa [mem_compl_iff, iff_false_intro (not_not.mpr heK), imp_false,
      subset_compl_iff_disjoint_right, not_disjoint_iff_nonempty_inter] at h'
  obtain ⟨e, heX, heH⟩ := h (Hᶜ) (by rwa [compl_compl]) heH
  exact heH (hXH heX)

theorem Flat.subset_hyperplane_of_ne_univ (hF : M.Flat F) (h : F ≠ univ) :
    ∃ H, M.Hyperplane H ∧ F ⊆ H :=
  by
  obtain ⟨e, he⟩ := (ne_univ_iff_exists_not_mem _).mp h
  rw [← hF.cl] at he
  obtain ⟨H, hH, hFH, -⟩ := exists_hyperplane_sep_of_not_mem_cl he
  exact ⟨H, hH, hFH⟩

theorem subset_hyperplane_iff_cl_ne_univ : M.cl Y ≠ univ ↔ ∃ H, M.Hyperplane H ∧ Y ⊆ H :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨H, hH, hYH⟩ := (M.flat_of_cl Y).subset_hyperplane_of_ne_univ h
    exact ⟨H, hH, (M.subset_cl Y).trans hYH⟩
  rintro ⟨H, hH, hYH⟩ hY
  refine' hH.ssubset_univ.not_subset _
  rw [← hH.flat.cl]
  exact hY.symm.trans_subset (M.cl_mono hYH)

theorem coindep_iff_cl_compl_eq_univ : M.Coindep I ↔ M.cl (Iᶜ) = univ :=
  by
  simp_rw [← base_subset_iff_cl_eq_univ, subset_compl_iff_disjoint_left, coindep]
  tauto

theorem Hyperplane.inter_right_covby_of_inter_left_covby (hH₁ : M.Hyperplane H₁)
    (hH₂ : M.Hyperplane H₂) (h : M.Covby (H₁ ∩ H₂) H₁) : M.Covby (H₁ ∩ H₂) H₂ :=
  by
  obtain rfl | hne := eq_or_ne H₁ H₂
  assumption
  have hssu : H₁ ∩ H₂ ⊂ H₂ :=
    by
    refine' (inter_subset_right _ _).ssubset_of_ne fun h'' => hne _
    rw [inter_eq_right_iff_subset, ← le_iff_subset] at h''
    rw [eq_of_le_of_not_lt h'' (hH₂.not_ssubset hH₁)]
  refine' ⟨hH₁.flat.inter hH₂.flat, hH₂.flat, hssu, fun F hF hssF hFH₂ => _⟩
  by_contra' h'
  obtain ⟨x, hxF, hx⟩ := exists_of_ssubset (hssF.ssubset_of_ne (Ne.symm h'.1))
  obtain ⟨y, hyH₂, hy⟩ := exists_of_ssubset (hFH₂.ssubset_of_ne h'.2)
  obtain ⟨z, hzH₁, hz⟩ := exists_of_ssubset h.ssubset
  have hzcl : M.cl (insert z (H₁ ∩ H₂)) = H₁ := h.cl_insert_eq ⟨hzH₁, hz⟩
  have hxH₁ : x ∉ H₁ := fun hxH₁ => hx ⟨hxH₁, hFH₂ hxF⟩
  have h₁ : z ∉ M.cl (insert x (H₁ ∩ H₂)) := by
    intro hz'
    apply hxH₁
    have h' := cl_exchange ⟨hz', by rwa [(hH₁.flat.inter hH₂.flat).cl]⟩
    rw [h.cl_insert_eq ⟨hzH₁, hz⟩] at h'
    exact h'.1
  have hycl : y ∈ M.cl (insert z (insert x (H₁ ∩ H₂))) \ M.cl (insert x (H₁ ∩ H₂)) :=
    by
    refine' ⟨_, fun hy' => hy _⟩
    · rw [insert_comm, ← cl_insert_cl_eq_cl_insert, hzcl, hH₁.cl_insert_eq_univ hxH₁]
      exact mem_univ _
    exact hF.cl_subset_of_subset (insert_subset.mpr ⟨hxF, hssF⟩) hy'
  refine'
    hz
      ⟨hzH₁,
        mem_of_mem_of_subset (cl_exchange hycl)
          ((diff_subset _ _).trans (hH₂.flat.cl_subset_of_subset _))⟩
  rw [insert_subset, insert_subset]
  exact ⟨hyH₂, hFH₂ hxF, inter_subset_right _ _⟩

theorem Hyperplane.inter_covby_comm (hH₁ : M.Hyperplane H₁) (hH₂ : M.Hyperplane H₂) :
    M.Covby (H₁ ∩ H₂) H₁ ↔ M.Covby (H₁ ∩ H₂) H₂ :=
  ⟨hH₁.inter_right_covby_of_inter_left_covby hH₂,
    by
    rw [inter_comm]
    intro h
    exact hH₂.inter_right_covby_of_inter_left_covby hH₁ h⟩

end Hyperplane

section FromAxioms

theorem matroid_of_flat_aux [Finite E] (flat : Set E → Prop) (univ_flat : flat univ)
    (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : Set E) :
    flat (⋂₀ { F | flat F ∧ X ⊆ F }) ∧ ∀ F₀, flat F₀ → (⋂₀ { F | flat F ∧ X ⊆ F } ⊆ F₀ ↔ X ⊆ F₀) :=
  by
  set F₁ := ⋂₀ { F | flat F ∧ X ⊆ F } with hF₁
  refine' ⟨_, fun F₀ hF₀ => ⟨fun hF₁F₀ => _, fun hXF => _⟩⟩
  · obtain ⟨F', ⟨hF', hYF'⟩, hmin⟩ :=
      finite.exists_minimal (fun F => flat F ∧ X ⊆ F) ⟨univ, univ_flat, subset_univ _⟩
    convert hF'
    refine' subset_antisymm (sInter_subset_of_mem ⟨hF', hYF'⟩) (subset_sInter _)
    rintro F ⟨hF, hYF⟩
    rw [hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _]
    · apply inter_subset_left
    apply inter_subset_right
  · refine' subset_trans (subset_sInter fun F h => _) hF₁F₀
    exact h.2
  apply sInter_subset_of_mem
  exact ⟨hF₀, hXF⟩

/-- A collection of sets satisfying the flat axioms determines a matroid -/
def matroidOfFlat [Finite E] (flat : Set E → Prop) (univ_flat : flat univ)
    (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
    (flat_partition :
      ∀ F₀ e,
        flat F₀ →
          e ∉ F₀ → ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
  matroidOfClOfFinite (fun X => ⋂₀ { F | flat F ∧ X ⊆ F })
    (fun X => subset_sInter fun F => And.right)
    (fun X Y hXY =>
      subset_sInter fun F hF => by
        apply sInter_subset_of_mem
        exact ⟨hF.1, hXY.trans hF.2⟩)
    (by
      refine' fun X => (subset_sInter fun F => And.right).antisymm' _
      simp only [subset_sInter_iff, mem_set_of_eq, and_imp]
      rintro F hF hXF
      apply sInter_subset_of_mem
      constructor; assumption
      apply sInter_subset_of_mem
      exact ⟨hF, hXF⟩)
    (by
      simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
        forall_exists_index]
      refine' fun X e f h F₀ hF₀ hXF₀ hfF₀ =>
        ⟨fun Ff hFf hfXf => _,
          ⟨F₀, hF₀, hXF₀, fun heF₀ => hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀, hXF₀⟩))⟩⟩
      obtain ⟨hFX, hX'⟩ := matroid_of_flat_aux flat univ_flat flat_inter X
      obtain ⟨hFXe, hXe'⟩ := matroid_of_flat_aux flat univ_flat flat_inter (insert e X)
      obtain ⟨hFXf, hXf'⟩ := matroid_of_flat_aux flat univ_flat flat_inter (insert f X)
      set FX := sInter { F | flat F ∧ X ⊆ F } with hFX_def
      set FXe := sInter { F | flat F ∧ insert e X ⊆ F } with hFXe_def
      set FXf := sInter { F | flat F ∧ insert f X ⊆ F } with hFXe_def
      apply (hXf' Ff hFf).mpr hfXf
      have heFXe : e ∈ FXe := mem_sInter.mpr fun _ hF => hF.2 (mem_insert _ _)
      have hfFXf : f ∈ FXf := mem_sInter.mpr fun _ hF => hF.2 (mem_insert _ _)
      have hXFX : X ⊆ FX := subset_sInter fun _ => And.right
      have hfFX : f ∉ FX := fun hfFX => hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX)
      have heFX : e ∉ FX := fun heFX => hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩))
      have hFXFXe : FX ⊆ FXe := by
        rw [hX' FXe hFXe]
        exact subset_sInter fun F hF => (subset_insert _ _).trans hF.2
      have hFXFXf : FX ⊆ FXf := by
        rw [hX' FXf hFXf]
        exact subset_sInter fun F hF => (subset_insert _ _).trans hF.2
      have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe, hXFX.trans hFXFXe⟩)
      have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩)
      suffices h_eq : FXf = FXe
      · rwa [h_eq]
      by_contra h_ne
      apply hfFX
      have hssu := ssubset_of_subset_of_ne hss h_ne
      obtain ⟨FXe', ⟨hFXe', heFX', hmin⟩, hunique⟩ := flat_partition FX e hFX heFX
      have hFXemin : ∀ F : Set E, flat F → FX ⊆ F → F ⊂ FXe → FX = F := fun F hF hFXF hFFXe =>
        hmin _ hF hFXF
          (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX')))
      rw [hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩] at hssu
      rwa [← hmin _ hFXf hFXFXf hssu] at hfFXf)

@[simp]
theorem matroidOfFlat_apply [Finite E] (flat : Set E → Prop) (univ_flat : flat univ)
    (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
    (flat_partition :
      ∀ F₀ e,
        flat F₀ →
          e ∉ F₀ → ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
    (matroidOfFlat flat univ_flat flat_inter flat_partition).Flat = flat :=
  by
  ext F
  simp_rw [matroid_of_flat, Matroid.flat_iff_cl_self, matroid_of_cl_of_finite_apply]
  refine' ⟨fun hF => _, fun hF => _⟩
  · rw [← hF]
    exact (matroid_of_flat_aux flat univ_flat flat_inter _).1
  exact (subset_sInter fun F' => And.right).antisymm' (sInter_subset_of_mem ⟨hF, rfl.subset⟩)

end FromAxioms

end Matroid

