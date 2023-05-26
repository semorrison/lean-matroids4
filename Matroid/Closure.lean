import Matroid.Basic
import Project.Mathlib.Data.Set.Basic

noncomputable section

open Classical

open BigOperators

open Set

namespace Matroid

variable {E : Type _} {M : Matroid E} {I J B C X Y : Set E} {e f x y : E}

/-- A flat is a maximal set having a given basis  -/
def Flat (M : Matroid E) (F : Set E) : Prop :=
  ∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F

/-- The closure of a set is the intersection of the flats containing it -/
def cl (M : Matroid E) (X : Set E) : Set E :=
  ⋂₀ { F | M.Flat F ∧ X ⊆ F }

theorem cl_def (M : Matroid E) : M.cl X = ⋂₀ { F | M.Flat F ∧ X ⊆ F } :=
  rfl

theorem mem_cl_iff_forall_mem_flat : e ∈ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp_rw [cl_def, mem_sInter, mem_set_of_eq, and_imp]

theorem subset_cl (M : Matroid E) (X : Set E) : X ⊆ M.cl X := by
  simp only [cl_def, subset_sInter_iff, mem_set_of_eq, and_imp, imp_self, imp_true_iff]

@[simp]
theorem cl_univ (M : Matroid E) : M.cl univ = univ :=
  (subset_univ _).antisymm (M.subset_cl _)

@[simp]
theorem cl_cl (M : Matroid E) (X : Set E) : M.cl (M.cl X) = M.cl X :=
  by
  refine' (subset_cl _ _).antisymm' fun e he => _
  rw [mem_cl_iff_forall_mem_flat] at *
  refine' fun F hF hXF => he _ hF fun f hf => _
  rw [mem_cl_iff_forall_mem_flat] at hf
  exact hf _ hF hXF

theorem cl_subset (M : Matroid E) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
  sInter_subset_sInter fun F hF => ⟨hF.1, h.trans hF.2⟩

theorem cl_mono (M : Matroid E) : Monotone M.cl := fun _ _ => M.cl_subset

theorem cl_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y := by
  simpa only [cl_cl] using M.cl_subset hXY

theorem cl_subset_cl_iff_subset_cl : M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
  ⟨fun h => (M.subset_cl _).trans h, cl_subset_cl⟩

theorem subset_cl_of_subset (M : Matroid E) (hXY : X ⊆ Y) : X ⊆ M.cl Y :=
  hXY.trans (M.subset_cl Y)

theorem mem_cl_of_mem (M : Matroid E) (h : e ∈ X) : e ∈ M.cl X :=
  (M.subset_cl X) h

theorem cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X :=
  by
  refine' (M.cl_mono (subset_insert _ _)).antisymm' _
  rw [← M.cl_cl X]
  exact M.cl_subset (insert_subset.mpr ⟨he, M.subset_cl _⟩)

@[simp]
theorem cl_union_cl_right_eq_cl_union (M : Matroid E) (X Y : Set E) :
    M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) :=
  by
  refine' (M.cl_mono (union_subset_union_right X (M.subset_cl _))).antisymm' _
  rw [← M.cl_cl (X ∪ Y)]
  exact
    M.cl_mono
      (union_subset ((subset_union_left _ _).trans (M.subset_cl _))
        (M.cl_mono (subset_union_right _ _)))

@[simp]
theorem cl_union_cl_left_eq_cl_union (M : Matroid E) (X Y : Set E) :
    M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) := by
  rw [union_comm, cl_union_cl_right_eq_cl_union, union_comm]

@[simp]
theorem cl_cl_union_cl_eq_cl_union (M : Matroid E) (X Y : Set E) :
    M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [cl_union_cl_left_eq_cl_union, cl_union_cl_right_eq_cl_union]

@[simp]
theorem cl_insert_cl_eq_cl_insert (M : Matroid E) (e : E) (X : Set E) :
    M.cl (insert e (M.cl X)) = M.cl (insert e X) := by
  simp_rw [← singleton_union, cl_union_cl_right_eq_cl_union]

@[simp]
theorem cl_diff_loops_eq_cl (M : Matroid E) (X : Set E) : M.cl (X \ M.cl ∅) = M.cl X := by
  rw [← union_empty (X \ M.cl ∅), ← cl_union_cl_right_eq_cl_union, diff_union_self,
    cl_union_cl_right_eq_cl_union, union_empty]

theorem mem_cl_self (M : Matroid E) (e : E) : e ∈ M.cl {e} :=
  (M.subset_cl {e}) (mem_singleton e)

theorem Indep.cl_eq_setOf_basis (hI : M.indep I) : M.cl I = { x | M.Basis I (insert x I) } :=
  by
  set F := { x | M.basis I (insert x I) } with hF
  have hIF : M.basis I F := by
    rw [basis_iff]
    refine'
      ⟨hI, fun e he => by
        rw [hF, mem_set_of, insert_eq_of_mem he]
        exact hI.basis_self, fun J hJ hIJ hJF => hIJ.antisymm fun e he => _⟩
    rw [basis.eq_of_subset_indep (hJF he) (hJ.subset (insert_subset.mpr ⟨he, hIJ⟩))
        (subset_insert _ _) subset.rfl]
    exact mem_insert _ _
  have hF : M.flat F :=
    by
    refine' fun J Y hJ hJY y hy =>
      indep.basis_of_forall_insert hI (subset_insert _ _) fun e he heI => _
    refine'
      (hIF.transfer hJ (subset_union_right _ _) (hJY.basis_union hJ)).insert_dep
        (mem_of_mem_of_subset he _) heI
    rw [diff_subset_iff, union_diff_self, insert_subset]
    exact ⟨Or.inr (Or.inl hy), subset_union_left _ _⟩
  rw [subset_antisymm_iff, cl, subset_sInter_iff]
  refine' ⟨sInter_subset_of_mem ⟨hF, hIF.subset⟩, _⟩
  rintro F' ⟨hF', hIF'⟩ e (he : M.basis I (insert e I))
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF'
  exact (hF' hJ (he.basis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))

theorem Indep.mem_cl_iff (hI : M.indep I) : x ∈ M.cl I ↔ M.indep (insert x I) → x ∈ I :=
  by
  rw [hI.cl_eq_set_of_basis, mem_set_of_eq]
  refine'
    ⟨fun h h' => _, fun h => hI.basis_of_forall_insert (subset_insert _ _) fun e he heI => he.2 _⟩
  · rw [h.eq_of_subset_indep h' (subset_insert _ _) subset.rfl]
    exact mem_insert _ _
  rw [← singleton_union, union_diff_right, mem_diff, mem_singleton_iff] at he
  rw [he.1] at heI⊢
  exact h heI

theorem Indep.mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) :
    e ∈ M.cl I ↔ ¬M.indep (insert e I) := by
  rw [hI.mem_cl_iff, (iff_false_iff _).mpr heI, imp_false]

theorem Indep.not_mem_cl_iff (hI : M.indep I) : e ∉ M.cl I ↔ e ∉ I ∧ M.indep (insert e I) := by
  rw [← not_iff_not, not_not_mem, and_comm', not_and, hI.mem_cl_iff, not_not_mem]

theorem Indep.not_mem_cl_iff_of_not_mem (hI : M.indep I) (heI : e ∉ I) :
    e ∉ M.cl I ↔ M.indep (insert e I) := by rw [hI.mem_cl_iff_of_not_mem heI, Classical.not_not]

theorem iInter_cl_eq_cl_iInter_of_iUnion_indep {ι : Type _} (I : ι → Set E)
    (h : M.indep (⋃ i, I i)) : (⋂ i, M.cl (I i)) = M.cl (⋂ i, I i) :=
  by
  have hi : ∀ i, M.indep (I i) := fun i => h.subset (subset_Union _ _)
  refine' subset.antisymm _ (subset_Inter fun i => M.cl_subset (Inter_subset _ _))
  rintro e he
  rw [mem_Inter] at he
  by_contra h'
  obtain hι | ⟨⟨i₀⟩⟩ := isEmpty_or_nonempty ι
  · haveI := hι
    apply h'
    rw [Inter_of_empty, cl_univ]
    exact mem_univ _
  have hiu : (⋂ i, I i) ⊆ ⋃ i, I i := (Inter_subset _ i₀).trans (subset_Union _ i₀)
  have hi_inter : M.indep (⋂ i, I i) := (hi i₀).Subset (Inter_subset _ _)
  rw [hi_inter.not_mem_cl_iff, mem_Inter, not_forall] at h'
  obtain ⟨⟨i₁, hei₁⟩, hei⟩ := h'
  have hdi₁ : ¬M.indep (insert e (I i₁)) := fun h_ind => hei₁ ((hi i₁).mem_cl_iff.mp (he i₁) h_ind)
  have heu : e ∉ ⋃ i, I i := fun he => hdi₁ (h.subset (insert_subset.mpr ⟨he, subset_Union _ _⟩))
  have hd_all : ∀ i, ¬M.indep (insert e (I i)) := fun i hind =>
    heu (mem_Union_of_mem _ ((hi i).mem_cl_iff.mp (he i) hind))
  have hb : M.basis (⋃ i, I i) (insert e (⋃ i, I i)) :=
    by
    have h' := M.cl_subset (subset_Union _ _) (he i₀)
    rwa [h.cl_eq_set_of_basis] at h'
  obtain ⟨I', hI', hssI', hI'ss⟩ :=
    hei.exists_basis_subset_union_basis (insert_subset_insert hiu) hb
  rw [insert_union, union_eq_right_iff_subset.mpr hiu] at hI'ss
  have hI'I : (I' \ ⋃ i, I i) = {e} :=
    by
    refine' subset.antisymm _ (singleton_subset_iff.mpr ⟨hssI' (mem_insert _ _), heu⟩)
    rwa [diff_subset_iff, union_singleton]
  obtain ⟨f, hfI, hf⟩ := hI'.eq_exchange_of_diff_eq_singleton hb hI'I
  have hf' : ∀ i, f ∈ I i :=
    by
    refine' fun i => by_contra fun hfi => hd_all i (hI'.indep.subset (insert_subset.mpr ⟨_, _⟩))
    · exact hssI' (mem_insert _ _)
    rw [← diff_singleton_eq_self hfi, diff_subset_iff, singleton_union]
    exact ((subset_Union _ i).trans_eq hf).trans (diff_subset _ _)
  exact hfI.2 (hssI' (Or.inr (by rwa [mem_Inter])))

theorem bInter_cl_eq_cl_sInter_of_sUnion_indep (Is : Set (Set E)) (h : M.indep (⋃₀ Is)) :
    (⋂ I ∈ Is, M.cl I) = M.cl (⋂₀ Is) :=
  by
  rw [sUnion_eq_Union] at h
  rw [bInter_eq_Inter, sInter_eq_Inter]
  exact Inter_cl_eq_cl_Inter_of_Union_indep (fun x : Is => coe x) h

theorem inter_cl_eq_cl_inter_of_union_indep (h : M.indep (I ∪ J)) :
    M.cl I ∩ M.cl J = M.cl (I ∩ J) :=
  by
  rw [inter_eq_Inter, inter_eq_Inter]; rw [union_eq_Union] at h
  convert Inter_cl_eq_cl_Inter_of_Union_indep (fun b => cond b I J) (by simpa)
  ext; cases x <;> simp

theorem Basis.cl (hIX : M.Basis I X) : M.cl I = M.cl X :=
  (M.cl_subset hIX.Subset).antisymm
    (cl_subset_cl fun x hx => hIX.indep.mem_cl_iff.mpr fun h => hIX.mem_of_insert_indep hx h)

theorem Basis.mem_cl_iff (hIX : M.Basis I X) : e ∈ M.cl X ↔ M.indep (insert e I) → e ∈ I := by
  rw [← hIX.cl, hIX.indep.mem_cl_iff]

theorem Basis.mem_cl_iff_of_not_mem (hIX : M.Basis I X) (he : e ∉ X) :
    e ∈ M.cl X ↔ ¬M.indep (insert e I) :=
  by
  rw [hIX.mem_cl_iff]
  exact ⟨fun h h' => he (hIX.subset (h h')), fun h h' => (h h').elim⟩

theorem Basis.subset_cl (hI : M.Basis I X) : X ⊆ M.cl I :=
  by
  rw [hI.cl]
  exact M.subset_cl X

theorem Indep.basis_cl (hI : M.indep I) : M.Basis I (M.cl I) :=
  by
  refine' hI.basis_of_forall_insert (M.subset_cl _) fun e he heI => he.2 _
  rw [mem_diff, hI.mem_cl_iff] at he
  exact he.1 heI

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem cl_eq_setOf_indep_not_indep (M : Matroid E) (X : Set E) :
    M.cl X = X ∪ { e | ∃ (I : _)(_ : I ⊆ X), M.indep I ∧ ¬M.indep (insert e I) } :=
  by
  refine'
    subset_antisymm (fun e he => (em (e ∈ X)).elim Or.inl fun heX => Or.inr _)
      (union_subset (M.subset_cl X) _)
  · obtain ⟨I, hI⟩ := M.exists_basis X
    refine' ⟨I, hI.subset, hI.indep, _⟩
    refine'
      hI.indep.basis_cl.dep_of_ssubset (ssubset_insert (not_mem_subset hI.subset heX))
        (insert_subset.mpr ⟨by rwa [hI.cl], M.subset_cl I⟩)
  rintro e ⟨I, hIX, hI, hIe⟩
  refine' (M.cl_subset hIX) _
  rw [hI.mem_cl_iff]
  exact fun h => (hIe h).elim

theorem Indep.basis_of_subset_cl (hI : M.indep I) (hIX : I ⊆ X) (h : X ⊆ M.cl I) : M.Basis I X :=
  hI.basis_cl.basis_subset hIX h

theorem Indep.base_of_cl_eq_univ (hI : M.indep I) (h : M.cl I = univ) : M.base I :=
  by
  rw [base_iff_basis_univ]
  refine' hI.basis_of_subset_cl (subset_univ _) (by rw [h])

theorem Basis.basis_cl (hI : M.Basis I X) : M.Basis I (M.cl X) :=
  by
  rw [← hI.cl]
  exact hI.indep.basis_cl

theorem basis_iff_basis_cl_of_subset (hIX : I ⊆ X) : M.Basis I X ↔ M.Basis I (M.cl X) :=
  ⟨fun h => h.basis_cl, fun h => h.basis_subset hIX (subset_cl _ _)⟩

theorem Basis.basis_of_cl_eq_cl (hI : M.Basis I X) (hY : I ⊆ Y) (h : M.cl X = M.cl Y) :
    M.Basis I Y := by
  rw [basis_iff_basis_cl_of_subset hY, ← h]
  exact hI.basis_cl

theorem Base.cl (hB : M.base B) : M.cl B = univ :=
  by
  rw [(base_iff_basis_univ.mp hB).cl]
  exact eq_univ_of_univ_subset (M.subset_cl _)

theorem Base.mem_cl (hB : M.base B) (e : E) : e ∈ M.cl B :=
  by
  rw [base.cl hB]
  exact mem_univ e

theorem Base.cl_of_supset (hB : M.base B) (hBX : B ⊆ X) : M.cl X = univ :=
  eq_univ_of_univ_subset (subset_trans (by rw [hB.cl]) (M.cl_mono hBX))

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (B «expr ⊆ » X) -/
theorem base_subset_iff_cl_eq_univ : (∃ (B : _)(_ : B ⊆ X), M.base B) ↔ M.cl X = univ :=
  by
  refine' ⟨fun ⟨B, hBX, hB⟩ => hB.cl_of_supset hBX, fun h => _⟩
  obtain ⟨B, hBX⟩ := M.exists_basis X
  use B, hBX.subset
  rw [base_iff_basis_univ, ← h, ← hBX.cl]
  exact hBX.indep.basis_cl

theorem mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : f ∈ M.cl (insert e X) :=
  by
  have hf : f ∉ M.cl X := fun hf => he (by rwa [← cl_insert_eq_of_mem_cl hf])
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.cl, hI.indep.not_mem_cl_iff] at he hf
  have he' := hI.insert_basis_insert he.2
  rw [← he'.cl, he'.indep.mem_cl_iff, mem_insert_iff]
  have hf' := hI.insert_basis_insert hf.2
  rw [← hf'.cl, hf'.indep.mem_cl_iff, insert_comm, mem_insert_iff] at hef
  intro h'
  obtain rfl | heI := hef h'
  · exact Or.inl rfl
  exact (he.1 heI).elim

theorem cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X) : f ∈ M.cl (insert e X) \ M.cl X :=
  by
  refine' ⟨mem_cl_insert he.2 he.1, fun hf => _⟩
  rw [cl_insert_eq_of_mem_cl hf, diff_self] at he
  exact not_mem_empty _ he

theorem cl_exchange_iff : e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
  ⟨cl_exchange, cl_exchange⟩

theorem cl_insert_eq_cl_insert_of_mem (he : e ∈ M.cl (insert f X) \ M.cl X) :
    M.cl (insert e X) = M.cl (insert f X) := by
  simp_rw [subset_antisymm_iff, cl_subset_cl_iff_subset_cl, insert_subset,
    and_iff_left (M.subset_cl_of_subset (subset_insert _ _)), and_iff_right he.1,
    iff_true_intro (cl_exchange he).1]

theorem cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X :=
  by
  refine' (M.cl_mono (diff_subset _ _)).antisymm _
  have h' := M.cl_mono (insert_subset.mpr ⟨h, M.subset_cl _⟩)
  rw [insert_diff_singleton, cl_cl] at h'
  exact (M.cl_mono (subset_insert _ _)).trans h'

theorem mem_cl_diff_singleton_iff_cl (he : e ∈ X) : e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
  ⟨cl_diff_singleton_eq_cl, fun h => by
    rw [h]
    exact subset_cl _ _ he⟩

theorem indep_iff_cl_diff_ne_forall : M.indep I ↔ ∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I :=
  by
  refine' ⟨fun h e heI h_eq => _, fun h => _⟩
  · have h' := (h.diff {e}).basis_cl
    rw [h_eq] at h'
    have h'' := h'.mem_of_insert_indep (M.subset_cl _ heI)
    simp_rw [insert_diff_singleton, mem_diff, mem_singleton, not_true, and_false_iff,
      insert_eq_of_mem heI] at h''
    exact h'' h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine' hJ.subset.antisymm' fun e he => by_contra fun heJ => _
  have hJIe : J ⊆ I \ {e} := subset_diff_singleton hJ.subset heJ
  have hcl := h e he
  rw [Ne.def, ← mem_cl_diff_singleton_iff_cl he] at hcl
  have hcl' := not_mem_subset (M.cl_mono hJIe) hcl
  rw [hJ.cl] at hcl'
  exact hcl' (M.subset_cl I he)

theorem indep_iff_not_mem_cl_diff_forall : M.indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
  by
  rw [indep_iff_cl_diff_ne_forall]
  exact
    ⟨fun h => fun x hxI => by
      rw [mem_cl_diff_singleton_iff_cl hxI]
      exact h x hxI, fun h x hxI =>
      by
      rw [Ne.def, ← mem_cl_diff_singleton_iff_cl hxI]
      exact h x hxI⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (J «expr ⊂ » I) -/
theorem indep_iff_cl_sSubset_sSubset_forall : M.indep I ↔ ∀ (J) (_ : J ⊂ I), M.cl J ⊂ M.cl I :=
  by
  refine'
    ⟨fun hI J hJI => _, fun h =>
      indep_iff_cl_diff_ne_forall.mpr fun x hx => (h _ <| diff_singleton_ssubset.2 hx).Ne⟩
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
  exact
    (M.cl_subset (subset_diff_singleton hJI.subset heJ)).trans_ssubset
      ((M.cl_subset (diff_subset I {e})).ssubset_of_ne (indep_iff_cl_diff_ne_forall.mp hI e heI))

theorem Indep.insert_indep_iff_of_not_mem (hI : M.indep I) (he : e ∉ I) :
    M.indep (insert e I) ↔ e ∉ M.cl I :=
  ⟨fun h => hI.not_mem_cl_iff.mpr ⟨he, h⟩, fun h => (hI.not_mem_cl_iff.mp h).2⟩

theorem Indep.cl_diff_singleton_sSubset (hI : M.indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂ M.cl I :=
  ssubset_of_subset_of_ne (M.cl_mono (diff_subset _ _)) (indep_iff_cl_diff_ne_forall.mp hI _ he)

theorem Indep.cl_sSubset_sSubset (hI : M.indep I) (hJI : J ⊂ I) : M.cl J ⊂ M.cl I :=
  indep_iff_cl_sSubset_sSubset_forall.mp hI J hJI

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (J «expr ⊆ » I) -/
theorem basis_iff_cl : M.Basis I X ↔ I ⊆ X ∧ X ⊆ M.cl I ∧ ∀ (J) (_ : J ⊆ I), X ⊆ M.cl J → J = I :=
  by
  constructor
  · refine' fun h => ⟨h.Subset, h.subset_cl, fun J hJI hXJ => hJI.antisymm fun e heI => _⟩
    rw [(h.indep.subset hJI).cl_eq_setOf_basis] at hXJ
    exact
      (h.subset.trans hXJ heI : M.basis _ _).mem_of_insert_indep (mem_insert _ _)
        (h.indep.subset (insert_subset.mpr ⟨heI, hJI⟩))
  rintro ⟨hIX, hXI, hmin⟩
  refine' indep.basis_of_forall_insert _ hIX _
  · rw [indep_iff_cl_diff_ne_forall]
    intro e he hecl
    rw [← hmin _ (diff_subset _ _) (hXI.trans_eq hecl.symm)] at he
    exact he.2 (mem_singleton e)
  exact fun e he hi =>
    he.2 ((hi.Subset (subset_insert _ _)).basis_cl.mem_of_insert_indep (hXI he.1) hi)

theorem basis_union_iff_indep_cl : M.Basis I (I ∪ X) ↔ M.indep I ∧ X ⊆ M.cl I :=
  by
  refine' ⟨fun h => ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, _⟩
  rw [basis_iff_cl]
  rintro ⟨hI, hXI⟩
  refine'
    ⟨subset_union_left _ _, union_subset (M.subset_cl _) hXI, fun J hJI hJ => by_contra fun h' => _⟩
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset (hJI.ssubset_of_ne h')
  have heJ' : e ∈ M.cl J := hJ (Or.inl heI)
  refine' indep_iff_not_mem_cl_diff_forall.mp hI e heI (mem_of_mem_of_subset heJ' _)
  exact M.cl_subset (subset_diff_singleton hJI heJ)

theorem basis_iff_indep_cl : M.Basis I X ↔ M.indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
  ⟨fun h => ⟨h.indep, h.subset_cl, h.Subset⟩, fun h =>
    (basis_union_iff_indep_cl.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩

theorem Basis.eq_of_cl_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) : J = I :=
  (basis_iff_cl.mp hI).2.2 J hJI hJ

theorem empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.cl ∅ :=
  by
  simp only [basis_iff_cl, empty_subset, true_and_iff, and_iff_left_iff_imp]
  exact fun h J hJ hXJ => subset_empty_iff.mp hJ

theorem eq_of_cl_eq_cl_forall {M₁ M₂ : Matroid E} (h : ∀ X, M₁.cl X = M₂.cl X) : M₁ = M₂ :=
  eq_of_indep_iff_indep_forall fun I => by simp_rw [indep_iff_cl_diff_ne_forall, h]

section FromAxioms

theorem cl_diff_singleton_eq_cl' (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X) {x : E} {I : Set E}
    (h : x ∈ cl (I \ {x})) : cl (I \ {x}) = cl I :=
  by
  refine' (cl_mono _ _ (diff_subset _ _)).antisymm _
  have h' := cl_mono _ _ (insert_subset.mpr ⟨h, subset_cl _⟩)
  rw [insert_diff_singleton, cl_idem] at h'
  exact (cl_mono _ _ (subset_insert _ _)).trans h'

/-- A set is independent relative to a closure function if none of its elements are contained in
  the closure of their removal -/
def ClIndep (cl : Set E → Set E) (I : Set E) : Prop :=
  ∀ e ∈ I, e ∉ cl (I \ {e})

theorem clIndep_mono {cl : Set E → Set E} (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) {I J : Set E}
    (hJ : ClIndep cl J) (hIJ : I ⊆ J) : ClIndep cl I := fun e heI hecl =>
  hJ e (hIJ heI) (cl_mono (diff_subset_diff_left hIJ) hecl)

theorem clIndep_aux {e : E} {I : Set E} {cl : Set E → Set E}
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
    (h : ClIndep cl I) (heI : ¬ClIndep cl (insert e I)) : e ∈ cl I :=
  by
  have he : e ∉ I := by
    intro he
    rw [insert_eq_of_mem he] at heI
    exact heI h
  rw [cl_indep] at heI
  push_neg  at heI
  obtain ⟨f, ⟨rfl | hfI, hfcl⟩⟩ := heI
  · rwa [insert_diff_self_of_not_mem he] at hfcl
  have hne : e ≠ f := by
    rintro rfl
    exact he hfI
  rw [← insert_diff_singleton_comm hne] at hfcl
  convert(cl_exchange (I \ {f}) e f ⟨hfcl, h f hfI⟩).1
  rw [insert_diff_singleton, insert_eq_of_mem hfI]

/-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
def matroidOfCl (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
    (cl_indep_maximal :
      ∀ ⦃I X⦄,
        ClIndep cl I → I ⊆ X → (maximals (· ⊆ ·) { J | ClIndep cl J ∧ I ⊆ J ∧ J ⊆ X }).Nonempty) :
    Matroid E :=
  matroidOfIndep (ClIndep cl) (fun e he _ => not_mem_empty _ he)
    (fun I J hJ hIJ => clIndep_mono cl_mono hJ hIJ)
    (by
      refine' fun I I' hI hIn hI'm => _
      obtain ⟨B, hB⟩ := cl_indep_maximal hI (subset_union_left I I')
      have hB' : B ∈ maximals (· ⊆ ·) { J | cl_indep cl J } :=
        by
        refine' ⟨hB.1.1, fun B' hB' hBB' e heB' => by_contra fun heB => _⟩
        have he' : e ∈ cl I' :=
          by
          refine'
            (em (e ∈ I')).elim (fun heI' => (subset_cl I') heI') fun heI' =>
              cl_indep_aux cl_exchange hI'm.1 fun hi => _
          exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _))
        have hI'B : I' ⊆ cl B :=
          by
          refine' fun f hf =>
            (em (f ∈ B)).elim (fun h' => subset_cl B h') fun hfB' =>
              cl_indep_aux cl_exchange hB.1.1 fun hi => hfB' _
          refine'
            hB.2 ⟨hi, hB.1.2.1.trans (subset_insert _ _), _⟩ (subset_insert _ _) (mem_insert _ _)
          exact insert_subset.mpr ⟨Or.inr hf, hB.1.2.2⟩
        have heBcl := (cl_idem B).Subset ((cl_mono hI'B) he')
        refine' cl_indep_mono cl_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _
        rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB]
      obtain ⟨f, hfB, hfI⟩ :=
        exists_of_ssubset
          (hB.1.2.1.ssubset_of_ne
            (by
              rintro rfl
              exact hIn hB'))
      refine' ⟨f, ⟨_, hfI⟩, cl_indep_mono cl_mono hB.1.1 (insert_subset.mpr ⟨hfB, hB.1.2.1⟩)⟩
      exact Or.elim (hB.1.2.2 hfB) (False.elim ∘ hfI) id)
    fun I X hI hIX => cl_indep_maximal hI hIX

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem clIndep_cl_eq {cl : Set E → Set E} (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
    (cl_indep_maximal :
      ∀ ⦃I X⦄,
        ClIndep cl I → I ⊆ X → (maximals (· ⊆ ·) { J | ClIndep cl J ∧ I ⊆ J ∧ J ⊆ X }).Nonempty)
    (X : Set E) :
    cl X = X ∪ { e | ∃ (I : _)(_ : I ⊆ X), ClIndep cl I ∧ ¬ClIndep cl (insert e I) } :=
  by
  ext f
  refine'
    ⟨fun h => (em (f ∈ X)).elim Or.inl fun hf => Or.inr _, fun h =>
      Or.elim h (fun g => subset_cl X g) _⟩
  · have hd : ¬cl_indep cl (insert f X) :=
      by
      refine' fun hi => hi f (mem_insert _ _) _
      convert h
      rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf]
    obtain ⟨I, hI⟩ := cl_indep_maximal (fun e he h' => not_mem_empty _ he) (empty_subset X)
    have hXI : X ⊆ cl I :=
      by
      refine' fun x hx => (em (x ∈ I)).elim (fun h' => subset_cl _ h') fun hxI => _
      refine' cl_indep_aux cl_exchange hI.1.1 fun hi => hxI _
      refine' hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _)
      exact insert_subset.mpr ⟨hx, hI.1.2.2⟩
    have hfI : f ∈ cl I := (cl_mono hXI).trans_eq (cl_idem I) h
    refine' ⟨I, hI.1.2.2, hI.1.1, fun hi => hf (hi f (mem_insert f _) _).elim⟩
    rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self]
    exact not_mem_subset hI.1.2.2 hf
  rintro ⟨I, hIX, hI, hfI⟩
  exact (cl_mono hIX) (cl_indep_aux cl_exchange hI hfI)

@[simp]
theorem matroidOfCl_apply {cl : Set E → Set E} (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
    (cl_indep_maximal :
      ∀ ⦃I X⦄,
        ClIndep cl I → I ⊆ X → (maximals (· ⊆ ·) { J | ClIndep cl J ∧ I ⊆ J ∧ J ⊆ X }).Nonempty) :
    (matroidOfCl cl subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).cl = cl :=
  by
  ext1 X
  rw [(cl_indep_cl_eq subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal X : cl X = _),
    matroid_of_cl, Matroid.cl_eq_setOf_indep_not_indep]
  simp

@[simp]
theorem matroidOfCl_indep_iff {cl : Set E → Set E} (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
    (cl_indep_maximal :
      ∀ ⦃I X⦄,
        ClIndep cl I → I ⊆ X → (maximals (· ⊆ ·) { J | ClIndep cl J ∧ I ⊆ J ∧ J ⊆ X }).Nonempty)
    {I : Set E} :
    (matroidOfCl cl subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).indep I ↔
      ClIndep cl I :=
  by rw [matroid_of_cl, matroid_of_indep_apply]

/-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
def matroidOfClOfIndepBounded (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) (n : ℕ)
    (hn : ∀ I, ClIndep cl I → I.Finite ∧ I.ncard ≤ n) : Matroid E :=
  matroidOfCl cl subset_cl cl_mono cl_idem cl_exchange
    (existsMaximalSubsetProperty_of_bounded ⟨n, hn⟩)

@[simp]
theorem matroidOfClOfIndepBounded_apply (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) (n : ℕ)
    (hn : ∀ I, ClIndep cl I → I.Finite ∧ I.ncard ≤ n) :
    (matroidOfClOfIndepBounded cl subset_cl cl_mono cl_idem cl_exchange n hn).cl = cl := by
  simp [matroid_of_cl_of_indep_bounded]

instance (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X) (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y)
    (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) (n : ℕ)
    (hn : ∀ I, ClIndep cl I → I.Finite ∧ I.ncard ≤ n) :
    Matroid.FiniteRk (matroidOfClOfIndepBounded cl subset_cl cl_mono cl_idem cl_exchange n hn) :=
  by
  obtain ⟨B, h⟩ :=
    (matroid_of_cl_of_indep_bounded cl subset_cl cl_mono cl_idem cl_exchange n hn).exists_base
  refine' h.finite_rk_of_finite (hn _ _).1
  simp_rw [matroid_of_cl_of_indep_bounded, matroid_of_cl, Matroid.base_iff_maximal_indep,
    matroid_of_indep_apply] at h
  exact h.1

/-- A finite matroid as defined by the closure axioms. -/
def matroidOfClOfFinite [Finite E] (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) : Matroid E :=
  matroidOfClOfIndepBounded cl subset_cl cl_mono cl_idem cl_exchange (Nat.card E) fun I hI =>
    ⟨toFinite _, by
      rw [← ncard_univ]
      exact ncard_le_of_subset (subset_univ _)⟩

@[simp]
theorem matroidOfClOfFinite_apply [Finite E] (cl : Set E → Set E) (subset_cl : ∀ X, X ⊆ cl X)
    (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
    (cl_exchange : ∀ X e f, f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
    (matroidOfClOfFinite cl subset_cl cl_mono cl_idem cl_exchange).cl = cl := by
  simp [matroid_of_cl_of_finite]

end FromAxioms

end Matroid

