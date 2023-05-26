import Project.Mathlib.Data.Set.Basic
import Project.Mathlib.Order.BooleanAlgebra
import Matroid.Maps.Quotients

/-!
# Projections, Loopifications and Pseudominors

For a matroid `M` on Type `E` and sets `C,D` in `M`, this file defines matroids `M ⟋ C` and
`M ⟍ D` which are obtained from `M` by contracting `C` and deleting `D` respectively, but then
adding back in `C` (or `D`) as a set containing only loops. We call these operations 'projection'
and 'loopification'.

The advantage of this over taking minors is that we stay in the Type `matroid E` rather than
changing the ground set and having to deal with type equality . In practice it seems
that many proofs that involve manipulating minors can be phrased only in terms of these modified
minor-like-objects, which we call pseudominors.

Kung's theorem and the matroid intersection theorem are currently both proved in this way.
(or at least will be once I fix them again)
-/


open Set

variable {E : Type _} {e f : E} {M N : Matroid E} {X Y D C F H B I J I₀ R : Set E}

namespace Matroid

section Restrict

@[class]
structure HasRestr (α β : Type _) where
  restr : α → β → α

-- mathport name: «expr ‖ »
infixl:75 " ‖ " => HasRestr.restr

instance {E : Type _} : HasRestr (Matroid E) (Set E) :=
  ⟨fun M E => M.lrestrict E⟩

@[simp]
theorem Lrestr.indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R :=
  lrestrict_indep_iff

theorem Indep.lrestr_indep_of_subset (hI : M.indep I) (hIR : I ⊆ R) : (M ‖ R).indep I :=
  Lrestr.indep_iff.mpr ⟨hI, hIR⟩

theorem Indep.lrestr_to_indep (h : (M ‖ R).indep I) : M.indep I :=
  (Lrestr.indep_iff.mp h).1

theorem Indep.lrestr_to_subset (h : (M ‖ R).indep I) : I ⊆ R :=
  (Lrestr.indep_iff.mp h).2

@[simp]
theorem lrestr_lrestr (M : Matroid E) (R₁ R₂ : Set E) : M ‖ R₁ ‖ R₂ = M ‖ (R₁ ∩ R₂) :=
  eq_of_indep_iff_indep_forall fun I => by simp [and_assoc']

theorem lrestr_lrestr_eq_lrestr_of_subset (M : Matroid E) {R₁ R₂ : Set E} (h : R₂ ⊆ R₁) :
    M ‖ R₁ ‖ R₂ = M ‖ R₂ := by rw [lrestr_lrestr, inter_eq_right_iff_subset.mpr h]

@[simp]
theorem lrestr_basis_iff : (M ‖ R).Basis I X ↔ M.Basis I (X ∩ R) :=
  by
  refine'
    ⟨fun h => indep.basis_of_maximal_subset _ _ _, fun h => indep.basis_of_maximal_subset _ _ _⟩
  · exact (lrestr.indep_iff.mp h.indep).1
  · exact subset_inter h.subset (lrestr.indep_iff.mp h.indep).2
  · intro J hJ hIJ hJXR
    rw [h.eq_of_subset_indep (hJ.lrestr_indep_of_subset (hJXR.trans (inter_subset_right _ _))) hIJ
        (hJXR.trans (inter_subset_left _ _))]
  · exact h.indep.lrestr_indep_of_subset (h.subset.trans (inter_subset_right _ _))
  · exact h.subset.trans (inter_subset_left _ _)
  intro J hJ hIJ hJX
  rw [h.eq_of_subset_indep (lrestr.indep_iff.mp hJ).1 hIJ (subset_inter hJX _)]
  exact (lrestr.indep_iff.mp hJ).2

@[simp]
theorem Lrestr.base_iff : (M ‖ R).base B ↔ M.Basis B R :=
  Iff.rfl

@[simp]
theorem Lrestr.r_eq (M : Matroid E) (R X : Set E) : (M ‖ R).R X = M.R (X ∩ R) :=
  by
  obtain ⟨I, hI⟩ := (M ‖ R).exists_basis X
  rw [← hI.card, ← (lrestr_basis_iff.mp hI).card]

theorem Lrestr.r_eq_of_subset (M : Matroid E) {hXR : X ⊆ R} : (M ‖ R).R X = M.R X := by
  rw [lrestr.r_eq, inter_eq_left_iff_subset.mpr hXR]

@[simp]
theorem Lrestr.rk_eq (M : Matroid E) (R : Set E) : (M ‖ R).rk = M.R R := by
  rw [rk_def, lrestr.r_eq, univ_inter]

@[simp]
theorem Lrestr.nonloop_iff : (M ‖ R).Nonloop e ↔ M.Nonloop e ∧ e ∈ R := by
  rw [← indep_singleton, ← indep_singleton, lrestr.indep_iff, singleton_subset_iff]

@[simp]
theorem Lrestr.loop_iff : (M ‖ R).Loop e ↔ M.Loop e ∨ e ∉ R := by
  rw [← not_iff_not, not_loop_iff, lrestr.nonloop_iff, not_or, not_loop_iff, Classical.not_not]

@[simp]
theorem Lrestr.cl_eq (M : Matroid E) (R X : Set E) : (M ‖ R).cl X = M.cl (X ∩ R) ∪ Rᶜ :=
  by
  obtain ⟨I, hI⟩ := (M ‖ R).exists_basis X
  simp_rw [← hI.cl, ← (lrestr_basis_iff.mp hI).cl]
  ext e
  rw [hI.indep.mem_cl_iff, lrestr.indep_iff, mem_union, (lrestr_basis_iff.mp hI).indep.mem_cl_iff,
    insert_subset, mem_compl_iff, and_imp, and_imp, ← imp_iff_or_not]
  exact ⟨fun h he hi => h hi he hI.indep.lrestr_to_subset, fun h hi heR hIR => h heR hi⟩

@[simp]
theorem Lrestr.loops_eq (M : Matroid E) (R : Set E) : (M ‖ R).cl ∅ᶜ = M.cl ∅ᶜ ∩ R := by
  rw [lrestr.cl_eq, empty_inter, compl_union, compl_compl]

@[simp]
theorem Lrestr.nonloops_eq (M : Matroid E) (R : Set E) : (M ‖ R).cl ∅ᶜ = M.cl ∅ᶜ ∩ R := by
  rw [lrestr.cl_eq, empty_inter, compl_union, compl_compl]

theorem Lrestr.weakImage (M : Matroid E) (R : Set E) : M ‖ R ≤w M := fun I => Indep.lrestr_to_indep

instance Lrestr.finiteRk {M : Matroid E} [FiniteRk M] {R : Set E} : FiniteRk (M ‖ R) :=
  (Lrestr.weakImage M R).FiniteRk

theorem lrestr_eq_lrestr_iff_symmDiff_loops : M ‖ X = M ‖ Y ↔ X ∆ Y ⊆ M.cl ∅ :=
  by
  simp_rw [eq_iff_indep_iff_indep_forall, lrestr.indep_iff, and_congr_right_iff]
  refine' ⟨fun h e => _, fun h I hI => _⟩
  · specialize h {e}
    simp only [indep_singleton, singleton_subset_iff] at h
    rintro (⟨heX, heY⟩ | ⟨heY, heX⟩)
    · rwa [iff_true_intro heX, iff_false_intro heY, true_iff_iff, imp_false, not_nonloop_iff] at h
    rwa [iff_true_intro heY, iff_false_intro heX, iff_true_iff, imp_false, not_nonloop_iff] at h
  exact
    ⟨fun hIX e heI => by_contra fun heY => hI.nonloop_of_mem heI (h (Or.inl ⟨hIX heI, heY⟩)),
      fun hIY e heI => by_contra fun heX => hI.nonloop_of_mem heI (h (Or.inr ⟨hIY heI, heX⟩))⟩

theorem lrestr_eq_lrestr_of_subset_of_diff_loops (hXY : X ⊆ Y) (h : Y \ X ⊆ M.cl ∅) :
    M ‖ Y = M ‖ X := by
  rwa [lrestr_eq_lrestr_iff_symm_diff_loops, Set.symmDiff_def, union_subset_iff,
    diff_eq_empty.mpr hXY, and_iff_left (empty_subset _)]

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem lrestr_eq_lrestr_iff {M₁ M₂ : Matroid E} :
    M₁ ‖ X = M₂ ‖ X ↔ ∀ (I) (_ : I ⊆ X), M₁.indep I ↔ M₂.indep I :=
  by
  refine' ⟨fun h I hIX => _, fun h => eq_of_indep_iff_indep_forall fun I => _⟩
  · apply_fun fun M : Matroid E => M.indep I  at h
    rwa [eq_iff_iff, lrestr.indep_iff, lrestr.indep_iff, ← (true_iff_iff _).mpr hIX, and_true_iff,
      and_true_iff] at h
  simp_rw [lrestr.indep_iff, and_congr_left_iff]
  exact h I

@[simp]
theorem lrestr_univ (M : Matroid E) : M ‖ (univ : Set E) = M :=
  by
  simp_rw [eq_iff_indep_iff_indep_forall, lrestr.indep_iff, and_iff_left (subset_univ _)]
  exact fun I => Iff.rfl

theorem lrestr_eq_self_iff (M : Matroid E) (R : Set E) : M ‖ R = M ↔ Rᶜ ⊆ M.cl ∅ :=
  by
  nth_rw 2 [← lrestr_univ M]
  rw [lrestr_eq_lrestr_iff_symm_diff_loops, symm_diff_univ]

end Restrict

section Loopify

@[class]
structure HasDel (α β : Type _) where
  del : α → β → α

-- mathport name: «expr ⟍ »
infixl:75 " ⟍ " => HasDel.del

/-- Matroid deletion is restriction to the complement -/
instance matroidDelLoopify {E : Type _} : HasDel (Matroid E) (Set E) :=
  ⟨fun M X => M ‖ Xᶜ⟩

/-- Matroid deletion of an element is deletion of the corresponding singleton set -/
instance delSingleton {E : Type _} : HasDel (Matroid E) E :=
  ⟨fun M e => M ⟍ ({e} : Set E)⟩

theorem loopify_eq_lrestr_compl (M : Matroid E) (D : Set E) : M ⟍ D = M ‖ Dᶜ :=
  rfl

@[simp]
theorem loopify_elem (M : Matroid E) (e : E) : M ⟍ e = M ⟍ ({e} : Set E) :=
  rfl

@[simp]
theorem Loopify.base_iff : (M ⟍ D).base B ↔ M.Basis B (Dᶜ) :=
  Iff.rfl

@[simp]
theorem Loopify.indep_iff : (M ⟍ D).indep I ↔ Disjoint I D ∧ M.indep I := by
  rw [loopify_eq_lrestr_compl, lrestr.indep_iff, subset_compl_iff_disjoint_right, and_comm']

theorem Indep.of_loopify (h : (M ⟍ D).indep I) : M.indep I :=
  (Loopify.indep_iff.mp h).2

theorem Loopify.weakImage (M : Matroid E) (D : Set E) : M ⟍ D ≤w M :=
  Lrestr.weakImage _ _

@[simp]
theorem Loopify.empty (M : Matroid E) : M ⟍ (∅ : Set E) = M :=
  eq_of_indep_iff_indep_forall fun I => by simp

theorem Loopify.circuit_iff : (M ⟍ D).Circuit C ↔ M.Circuit C ∧ Disjoint C D ∨ ∃ e ∈ D, C = {e} :=
  by
  simp_rw [circuit_iff, loopify.indep_iff, not_and, exists_prop]
  constructor
  · rintro ⟨h₁, h₂⟩
    obtain h | ⟨e, heC, heD⟩ := (C ∩ D).eq_empty_or_nonempty
    · left
      rw [← disjoint_iff_inter_eq_empty] at h
      exact ⟨⟨h₁ h, fun I hIC => h₂ _ fun _ => hIC⟩, h⟩
    refine' Or.inr ⟨e, heD, _⟩
    obtain hss | rfl := (singleton_subset_iff.mpr heC).ssubset_or_eq
    swap
    rfl
    rw [h₂ {e} (fun hdj => False.elim _) hss.subset]
    rw [disjoint_singleton_left] at hdj
    exact hdj heD
  rintro (⟨⟨hdep, h⟩, hdj⟩ | ⟨e, heD, rfl⟩)
  · exact ⟨fun _ => hdep, fun I hdj' hIC => h _ (hdj' (disjoint_of_subset_left hIC hdj)) hIC⟩
  refine'
    ⟨fun h => (disjoint_singleton_left.mp h heD).elim, fun I hI hIe =>
      (subset_singleton_iff_eq.mp hIe).elim _ id⟩
  rintro rfl
  exact (hI (empty_disjoint _) M.empty_indep).elim

theorem Loopify.circuit_iff_of_disjoint (hC : Disjoint C D) : (M ⟍ D).Circuit C ↔ M.Circuit C :=
  by
  rw [loopify.circuit_iff]
  refine' ⟨fun h => h.elim And.left _, fun h => Or.inl ⟨h, hC⟩⟩
  rintro ⟨e, heD, rfl⟩
  refine' h.elim And.left (False.elim ∘ _)
  rintro ⟨f, hfD, hef⟩
  rw [hef, disjoint_singleton_left] at hC
  exact hC hfD

@[simp]
theorem Loopify.cl_eq (D X : Set E) : (M ⟍ D).cl X = M.cl (X \ D) ∪ D :=
  by
  ext e
  simp_rw [mem_cl_iff_exists_circuit, loopify.circuit_iff]
  constructor
  · rintro (heX | ⟨C, ⟨⟨hC, hCD⟩ | ⟨f, hfD, rfl⟩, hC'⟩⟩)
    ·
      exact
        (em (e ∈ D)).elim Or.inr fun heD =>
          Or.inl (mem_of_mem_of_subset (⟨heX, heD⟩ : e ∈ X \ D) (M.subset_cl _))
    · refine' Or.inl (mem_of_mem_of_subset (hC.subset_cl_diff_singleton e hC'.1) (M.cl_subset _))
      rw [subset_diff, diff_subset_iff, singleton_union]
      exact ⟨hC'.2, disjoint_of_subset_left (diff_subset _ _) hCD⟩
    rw [← mem_singleton_iff.mp hC'.1] at hfD
    exact Or.inr hfD
  by_cases heD : e ∈ D
  · exact fun _ => Or.inr ⟨{e}, Or.inr ⟨_, heD, rfl⟩, mem_singleton_of_eq rfl, by simp⟩
  rintro (heX | heD'); swap; exact (heD heD').elim
  rw [mem_cl_iff_exists_circuit] at heX
  obtain heXD | ⟨C, hC, heC, hCX⟩ := heX
  · exact Or.inl ((diff_subset _ _) heXD)
  refine' (em (e ∈ X)).elim Or.inl fun heX => Or.inr _
  refine' ⟨C, Or.inl ⟨hC, _⟩, heC, hCX.trans (insert_subset_insert (diff_subset _ _))⟩
  rw [← inter_union_diff C {e}, disjoint_union_left, inter_singleton_eq_of_mem heC,
    disjoint_singleton_left]
  rw [← singleton_union, ← diff_subset_iff] at hCX
  exact ⟨heD, disjoint_of_subset_left hCX disjoint_sdiff_left⟩

@[simp]
theorem Loopify.loop_iff : (M ⟍ D).Loop e ↔ M.Loop e ∨ e ∈ D :=
  by
  simp_rw [loop_iff_mem_cl_empty, loopify.cl_eq, empty_diff]
  rfl

@[simp]
theorem Loopify.nonloop_iff : (M ⟍ D).Nonloop e ↔ M.Nonloop e ∧ e ∉ D := by
  simp_rw [← not_loop_iff, loopify.loop_iff, not_or]

theorem subset_loops_of_loopify (M : Matroid E) (D : Set E) : D ⊆ (M ⟍ D).cl ∅ :=
  by
  rw [loopify.cl_eq]
  exact subset_union_right _ _

theorem loop_of_loopify (h : e ∈ D) : (M ⟍ D).Loop e :=
  by
  rw [loop_iff_mem_cl_empty]
  exact M.subset_loops_of_loopify D h

@[simp]
theorem Loopify.nonloops (M : Matroid E) (D : Set E) : (M ⟍ D).cl ∅ᶜ = M.cl ∅ᶜ \ D :=
  by
  ext
  simp_rw [mem_diff, mem_compl_iff, ← loop_iff_mem_cl_empty, ← not_or, not_iff_not,
    loopify.loop_iff]

theorem Loopify.basis_iff : (M ⟍ D).Basis I X ↔ Disjoint I D ∧ M.Basis I (X \ D) :=
  by
  simp_rw [basis_iff, loopify.indep_iff]
  constructor
  · rintro ⟨⟨hdj, hI⟩, hIX, h⟩
    exact
      ⟨hdj, hI, subset_diff.mpr ⟨hIX, hdj⟩, fun J hJ hIJ hJX =>
        h J ⟨disjoint_of_subset_left hJX disjoint_sdiff_left, hJ⟩ hIJ (hJX.trans (diff_subset _ _))⟩
  rintro ⟨hdj, hI, hIXD, h⟩
  exact
    ⟨⟨hdj, hI⟩, hIXD.trans (diff_subset _ _), fun J h' hIJ hJX =>
      h _ h'.2 hIJ (subset_diff.mpr ⟨hJX, h'.1⟩)⟩

theorem Loopify.basis_iff_of_disjoint (h : Disjoint X D) : (M ⟍ D).Basis I X ↔ M.Basis I X :=
  by
  rw [loopify.basis_iff]
  exact
    ⟨fun hI =>
      hI.2.basis_subset (hI.2.Subset.trans (diff_subset _ _)) (subset_diff.mpr ⟨subset.rfl, h⟩),
      fun hI =>
      ⟨disjoint_of_subset_left hI.Subset h,
        hI.basis_subset (subset_diff.mpr ⟨hI.Subset, disjoint_of_subset_left hI.Subset h⟩)
          (diff_subset _ _)⟩⟩

@[simp]
theorem Loopify.r_eq : (M ⟍ D).R X = M.R (X \ D) :=
  by
  obtain ⟨I, hI⟩ := (M ⟍ D).exists_basis X
  rw [← hI.r, hI.indep.r]
  rw [loopify.basis_iff] at hI
  rw [← hI.2.R, hI.2.indep.R]

theorem Loopify.eq_of_subset_loops (h : D ⊆ M.cl ∅) : M ⟍ D = M :=
  by
  refine' eq_of_indep_iff_indep_forall fun I => _
  rw [loopify.indep_iff]
  refine' ⟨And.right, fun hI => ⟨disjoint_of_subset_right h hI.disjoint_loops, hI⟩⟩

theorem loopify_eq_self_iff_subset_loops : M ⟍ D = M ↔ D ⊆ M.cl ∅ :=
  by
  refine' ⟨fun h e heD => _, loopify.eq_of_subset_loops⟩
  rw [← h, loopify.cl_eq]
  exact Or.inr heD

theorem Loopify.r_eq_of_disjoint (h : Disjoint X D) : (M ⟍ D).R X = M.R X := by
  rw [loopify.r_eq, sdiff_eq_left.mpr h]

@[simp]
theorem loopify_loopify (M : Matroid E) (D D' : Set E) : M ⟍ D ⟍ D' = M ⟍ (D ∪ D') :=
  by
  refine' eq_of_indep_iff_indep_forall fun I => _
  simp_rw [loopify.indep_iff, ← and_assoc']
  convert Iff.rfl
  rw [and_comm', disjoint_union_right]

theorem loopify_comm (M : Matroid E) (D D' : Set E) : M ⟍ D ⟍ D' = M ⟍ D' ⟍ D := by
  rw [loopify_loopify, union_comm, loopify_loopify]

theorem not_mem_of_indep_loopify_singleton (h : (M ⟍ ({e} : Set E)).indep I) : e ∉ I :=
  (loop_of_loopify (mem_singleton e)).not_mem_indep h

theorem dual_cl_eq_coloops_loopify (M : Matroid E) (X : Set E) : M﹡.cl X = X ∪ (M ⟍ X)﹡.cl ∅ :=
  by
  ext e
  refine' (em (e ∈ X)).elim (fun heX => iff_of_true (mem_cl_of_mem _ heX) (Or.inl heX)) fun heX => _
  simp_rw [mem_union, mem_dual_cl_iff_forall_circuit, empty_inter, iff_false_intro heX,
    false_or_iff, iff_false_intro not_nonempty_empty, imp_false, loopify.circuit_iff, exists_prop,
    nonempty_iff_ne_empty, Ne.def, ← disjoint_iff_inter_eq_empty]
  refine' ⟨_, fun h C hC heC hdj => _⟩
  · rintro h C (⟨hC, hCX⟩ | ⟨f, hfX, rfl⟩) heC
    · exact h C hC heC hCX.symm
    rw [mem_singleton_iff] at heC
    subst heC
    exact heX hfX
  exact h C (Or.inl ⟨hC, hdj.symm⟩) heC

theorem RFin.loopify (hX : M.RFin X) (D : Set E) : (M ⟍ D).RFin X :=
  hX.WeakImage (Loopify.weakImage _ _)

theorem RFin.of_loopify (hX : (M ⟍ D).RFin X) (hD : M.RFin D) : M.RFin X :=
  by
  obtain ⟨I, hI⟩ := (M ⟍ D).exists_basis X
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.of_loopify.subset_basis_of_subset hI.subset
  obtain ⟨ID, hID⟩ := M.exists_basis D
  refine' r_fin.subset _ hI.subset_cl
  rw [loopify.cl_eq, ← r_fin_cl_iff, cl_union_cl_left_eq_cl_union, ← cl_union_cl_right_eq_cl_union,
    ← hID.cl, cl_union_cl_right_eq_cl_union, r_fin_cl_iff]
  exact M.r_fin_of_finite (((hI.finite_of_r_fin hX).diffₓ _).union (hID.finite_of_r_fin hD))

end Loopify

section Project

@[class]
structure HasCon (α β : Type _) where
  con : α → β → α

-- mathport name: «expr ⟋ »
infixl:75 " ⟋ " => HasCon.con

/-- The matroid obtained from `M` by contracting all elements in `C` and replacing them with loops-/
def project (M : Matroid E) (C : Set E) :=
  (M﹡ ⟍ C)﹡ ‖ Cᶜ

instance {E : Type _} : HasCon (Matroid E) (Set E) :=
  ⟨fun M C => M.project C⟩

instance projElem {E : Type _} : HasCon (Matroid E) E :=
  ⟨fun M e => M ⟋ ({e} : Set E)⟩

/-- Project every element outside `R` -/
def projectTo (M : Matroid E) (R : Set E) : Matroid E :=
  M ⟋ Rᶜ

@[simp]
theorem project_elem (M : Matroid E) (e : E) : M ⟋ e = M ⟋ ({e} : Set E) :=
  rfl

@[simp]
theorem project.cl_eq (M : Matroid E) (C X : Set E) : (M ⟋ C).cl X = M.cl (X ∪ C) :=
  by
  change ((M﹡ ⟍ C)﹡ ‖ Cᶜ).cl X = M.cl (X ∪ C)
  rw [lrestr.cl_eq, compl_compl, dual_cl_eq_coloops_loopify, loopify_loopify, ← diff_eq,
    union_diff_self, dual_cl_eq_coloops_loopify, loopify_loopify, union_empty, empty_union,
    union_right_comm, diff_union_self, Set.ext_iff, union_comm C]
  refine' fun e =>
    (em (e ∈ X ∪ C)).elim (fun he => iff_of_true (Or.inl he) (M.subset_cl _ he)) fun he => _
  simp_rw [@mem_union _ _ (X ∪ C), iff_false_intro he, false_or_iff, mem_dual_cl_iff_forall_circuit,
    loopify.circuit_iff, empty_inter, iff_false_intro not_nonempty_empty, imp_false,
    dual_circuit_iff_cocircuit, imp_not_comm, not_or, not_and, not_exists, not_disjoint_iff]
  refine' ⟨fun h => by_contra fun hecl => _, fun h K heK => ⟨fun hK => _, _⟩⟩
  · obtain ⟨H, hH, hXCH, heH⟩ := exists_hyperplane_sep_of_not_mem_cl hecl
    obtain ⟨f, hf, hf'⟩ := (h (Hᶜ) heH).1 hH.compl_cocircuit
    exact hf (hXCH hf')
  · rw [← dual_dual M, mem_dual_cl_iff_forall_circuit] at h
    obtain ⟨f, hf, hf'⟩ := h K (dual_circuit_iff_cocircuit.mpr hK) heK
    exact ⟨f, hf', hf⟩
  rintro f hf rfl
  rw [mem_singleton_iff] at heK; subst heK
  exact he hf

@[simp]
theorem project_cl_eq_project (M : Matroid E) (C : Set E) : M ⟋ M.cl C = M ⟋ C :=
  eq_of_cl_eq_cl_forall fun X => by simp_rw [project.cl_eq, cl_union_cl_right_eq_cl_union]

@[simp]
theorem project_empty (M : Matroid E) : M ⟋ (∅ : Set E) = M :=
  eq_of_cl_eq_cl_forall fun X => by simp_rw [project.cl_eq, union_empty]

@[simp]
theorem project_project (M : Matroid E) (C₁ C₂ : Set E) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
  eq_of_cl_eq_cl_forall fun X => by
    rw [project.cl_eq, project.cl_eq, project.cl_eq, union_right_comm, union_assoc]

theorem project_isQuotient (M : Matroid E) (C : Set E) : M ⟋ C ≼ M :=
  by
  simp_rw [is_quotient, project.cl_eq]
  exact fun X => M.cl_mono (subset_union_left _ _)

theorem project_weakImage (M : Matroid E) (C : Set E) : M ⟋ C ≤w M :=
  (M.project_isQuotient C).WeakImage

theorem project_comm (M : Matroid E) (C₁ C₂ : Set E) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ := by
  rw [project_project, project_project, union_comm]

theorem project.contract_subset_loops (M : Matroid E) (C : Set E) : C ⊆ (M ⟋ C).cl ∅ :=
  by
  rw [project.cl_eq, empty_union]
  apply M.subset_cl

theorem Indep.project_indep_iff (hJ : M.indep J) :
    (M ⟋ J).indep I ↔ Disjoint I J ∧ M.indep (I ∪ J) :=
  by
  simp_rw [@indep_iff_not_mem_cl_diff_forall _ _ I, project.cl_eq,
    indep_iff_forall_subset_not_circuit]
  refine'
    ⟨fun h =>
      ⟨disjoint_iff_forall_ne.mpr _, fun C hCIJ hC =>
        hC.dep (hJ.subset fun e heC => (hCIJ heC).elim (fun heI => False.elim _) id)⟩,
      fun h e heI hecl => _⟩
  · rintro e heI _ heJ rfl
    exact h e heI (M.mem_cl_of_mem (Or.inr heJ))
  · refine' h e heI (M.cl_subset _ (hC.subset_cl_diff_singleton e heC))
    rw [diff_subset_iff, ← union_assoc, union_diff_self, union_assoc]
    exact subset_union_of_subset_right hCIJ _
  rw [← indep_iff_forall_subset_not_circuit, indep_iff_not_mem_cl_diff_forall] at h
  have heJ : e ∉ J := fun heJ => h.1.ne_of_mem heI heJ rfl
  rw [← diff_singleton_eq_self heJ, ← union_diff_distrib] at hecl
  exact h.2 _ (Or.inl heI) hecl

theorem Basis.project_indep_iff {J : Set E} (hJC : M.Basis J C) :
    (M ⟋ C).indep I ↔ Disjoint I J ∧ M.indep (I ∪ J) := by
  rw [← project_cl_eq_project, ← hJC.cl, project_cl_eq_project, hJC.indep.project_indep_iff]

theorem Indep.of_project (h : (M ⟋ C).indep I) : M.indep I :=
  h.WeakImage (project_weakImage _ _)

instance {M : Matroid E} [FiniteRk M] {C : Set E} : FiniteRk (M ⟋ C) :=
  let ⟨B, hB⟩ := (M ⟋ C).exists_base
  hB.finiteRk_of_finite hB.indep.of_project.Finite

theorem Basis.project_eq_project (hI : M.Basis I X) : M ⟋ I = M ⟋ X := by
  rw [← project_cl_eq_project, ← M.project_cl_eq_project X, hI.cl]

@[simp]
theorem project_loops_eq : (M ⟋ C).cl ∅ = M.cl C := by rw [project.cl_eq, empty_union]

theorem project.loop_iff : (M ⟋ C).Loop e ↔ e ∈ M.cl C := by
  rw [loop_iff_mem_cl_empty, project.cl_eq, empty_union]

theorem project.loop_of_mem_cl (he : e ∈ M.cl C) : (M ⟋ C).Loop e :=
  project.loop_iff.mpr he

theorem project.loop_of_mem (he : e ∈ C) : (M ⟋ C).Loop e :=
  project.loop_iff.mpr (mem_of_mem_of_subset he (M.subset_cl _))

theorem project.eq_of_subset_loops (h : C ⊆ M.cl ∅) : M ⟋ C = M := by
  rw [← project_cl_eq_project, cl_eq_loops_of_subset h, project_cl_eq_project, project_empty]

theorem project_eq_self_iff_subset_loops : M ⟋ C = M ↔ C ⊆ M.cl ∅ :=
  by
  refine' ⟨fun h e heC => _, project.eq_of_subset_loops⟩
  rw [← h, project_loops_eq]
  exact (M.subset_cl C) heC

theorem Indep.disjoint_project (hI : (M ⟋ C).indep I) : Disjoint I C :=
  by
  simp_rw [indep_iff_not_mem_cl_diff_forall, project.cl_eq] at hI
  rw [disjoint_iff_forall_ne]
  rintro x hxI _ hxC rfl
  exact hI x hxI (M.subset_cl _ (Or.inr hxC))

theorem union_indep_of_project (hI : (M ⟋ C).indep I) (hJC : M.Basis J C) : M.indep (I ∪ J) :=
  (hJC.project_indep_iff.mp hI).2

theorem Basis.project_indep_of_disjoint_indep (hJ : M.Basis J C) (hdj : Disjoint I J)
    (h_ind : M.indep (I ∪ J)) : (M ⟋ C).indep I :=
  hJ.project_indep_iff.mpr ⟨hdj, h_ind⟩

theorem project_indep_iff_forall :
    (M ⟋ C).indep I ↔ Disjoint I C ∧ ∀ I₀, M.Basis I₀ C → M.indep (I ∪ I₀) :=
  by
  refine' ⟨fun hI => ⟨hI.disjoint_project, fun I₀ hI₀ => union_indep_of_project hI hI₀⟩, fun h => _⟩
  obtain ⟨J, hJ⟩ := M.exists_basis C
  exact hJ.project_indep_iff.mpr ⟨disjoint_of_subset_right hJ.subset h.1, h.2 _ hJ⟩

theorem project_basis_of_basis (hI : M.Basis I (X ∪ C)) (hIC : M.Basis (I ∩ C) C) :
    (M ⟋ C).Basis (I \ C) X :=
  by
  rw [← hIC.project_eq_project, basis_iff_indep_cl, project.cl_eq, diff_union_inter,
    diff_subset_iff, union_comm, hI.cl, hIC.indep.project_indep_iff, diff_union_inter]
  exact
    ⟨⟨disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left, hI.indep⟩,
      (subset_union_left _ _).trans (M.subset_cl _), hI.subset⟩

theorem Basis.union_basis_of_project_basis (hJ : M.Basis J C) (hI : (M ⟋ C).Basis I X) :
    M.Basis (I ∪ J) (X ∪ C) := by
  simp_rw [basis_iff_indep_cl]
  refine' ⟨union_indep_of_project hI.indep hJ, _, union_subset_union hI.subset hJ.subset⟩
  simp_rw [basis_iff_indep_cl, project.cl_eq] at hI
  rw [← cl_union_cl_right_eq_cl_union, hJ.cl, cl_union_cl_right_eq_cl_union]
  exact union_subset hI.2.1 ((subset_union_right _ _).trans (M.subset_cl _))

theorem Indep.project_basis_of_disjoint_of_basis_union (hJ : M.indep J) (hdj : Disjoint I J)
    (hIJ : M.Basis (I ∪ J) (X ∪ J)) : (M ⟋ J).Basis I X :=
  by
  rw [basis_iff_indep_cl, hJ.project_indep_iff, project.cl_eq, hIJ.cl]
  refine' ⟨⟨hdj, hIJ.indep⟩, (subset_union_left _ _).trans (subset_cl _ _), _⟩
  refine'
    (subset_inter (subset_compl_iff_disjoint_right.mpr hdj)
          ((subset_union_left _ _).trans hIJ.subset)).trans
      _
  rw [← diff_eq_compl_inter, diff_subset_iff, union_comm]

theorem Basis.project_basis_of_disjoint_of_basis_union (hJ : M.Basis J C) (hdj : Disjoint I J)
    (hIJ : M.Basis (I ∪ J) (X ∪ J)) : (M ⟋ C).Basis I X :=
  by
  rw [← hJ.project_eq_project]
  exact hJ.indep.project_basis_of_disjoint_of_basis_union hdj hIJ

theorem project_basis_iff_forall :
    (M ⟋ C).Basis I X ↔ Disjoint I (M.cl C) ∧ ∀ J, M.Basis J C → M.Basis (I ∪ J) (X ∪ C) :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← project_cl_eq_project] at h
    refine' ⟨h.indep.disjoint_project, fun J hJ => _⟩
    rw [project_cl_eq_project] at h
    exact hJ.union_basis_of_project_basis h
  obtain ⟨J, hJ⟩ := M.exists_basis C
  have h' := h.2 J hJ
  refine'
    hJ.project_basis_of_disjoint_of_basis_union
      (disjoint_of_subset_right (hJ.subset.trans (subset_cl _ _)) h.1)
      (indep.basis_of_subset_cl h'.indep (union_subset_union_left _ fun e heI => _) _)
  · refine' ((subset_union_left I J).trans h'.subset heI).elim id fun heC => _
    exact (h.1.ne_of_mem heI ((M.subset_cl C) heC) rfl).elim
  rw [h'.cl, ← cl_union_cl_right_eq_cl_union, ← hJ.cl, cl_union_cl_right_eq_cl_union]
  exact M.subset_cl _

theorem RFin.project_cast_r_eq (hX : M.RFin X) (hC : M.RFin C) :
    ((M ⟋ C).R X : ℤ) = M.R (X ∪ C) - M.R C :=
  by
  obtain ⟨I, hI⟩ := (M ⟋ C).exists_basis X
  obtain ⟨I₀, hI₀⟩ := M.exists_basis C
  obtain ⟨h1, h2⟩ := project_basis_iff_forall.mp hI
  specialize h2 _ hI₀
  have hIfin := h2.finite_of_r_fin (hX.union hC)
  rw [← hI.r, hI.indep.r, ← h2.r, ← hI₀.r, hI₀.indep.r, h2.indep.r, ncard_union_eq]
  · simp
  · exact disjoint_of_subset_right (hI₀.subset.trans (M.subset_cl _)) h1
  · exact hIfin.subset (subset_union_left I I₀)
  exact hIfin.subset (subset_union_right I I₀)

@[simp]
theorem project_cast_r_eq (M : Matroid E) [FiniteRk M] (X C) :
    ((M ⟋ C).R X : ℤ) = M.R (X ∪ C) - M.R C :=
  (M.to_rFin X).project_cast_r_eq (M.to_rFin C)

theorem RFin.project (hX : M.RFin X) (C : Set E) : (M ⟋ C).RFin X :=
  hX.WeakImage (project_weakImage _ _)

theorem RFin.of_project (hX : (M ⟋ C).RFin X) (hC : M.RFin C) : M.RFin X :=
  by
  obtain ⟨I, hI⟩ := (M ⟋ C).exists_basis X
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.of_project.subset_basis_of_subset hI.subset
  obtain ⟨IC, hIC⟩ := M.exists_basis C
  refine' r_fin.subset _ hI.subset_cl
  rw [project.cl_eq, ← cl_union_cl_right_eq_cl_union, ← hIC.cl, cl_union_cl_right_eq_cl_union,
    r_fin_cl_iff]
  exact M.r_fin_of_finite ((hI.finite_of_r_fin hX).union (hIC.finite_of_r_fin hC))

theorem project.r_add_r_eq_r_union (M : Matroid E) [FiniteRk M] (C X : Set E) :
    (M ⟋ C).R X + M.R C = M.R (X ∪ C) := by
  zify
  simp

theorem Nonloop.indep_project_iff (he : M.Nonloop e) (heI : e ∉ I) :
    (M ⟋ e).indep I ↔ M.indep (insert e I) := by
  rw [project_elem, he.indep.project_indep_iff, union_singleton, disjoint_singleton_right,
    iff_true_intro heI, true_and_iff]

theorem Nonloop.r_project_add_one_eq [FiniteRk M] (he : M.Nonloop e) (X : Set E) :
    (M ⟋ e).R X + 1 = M.R (insert e X) := by
  zify
  rw [project_elem, project_cast_r_eq, nonloop_iff_r.mp he]
  simp

theorem Nonloop.cast_r_project_eq [FiniteRk M] (he : M.Nonloop e) (X : Set E) :
    ((M ⟋ e).R X : ℤ) = M.R (insert e X) - 1 :=
  by
  rw [← nonloop.r_project_add_one_eq he X]
  simp

theorem not_mem_of_indep_project_singleton (h : (M ⟋ e).indep I) : e ∉ I :=
  (project.loop_of_mem (mem_singleton e)).not_mem_indep h

theorem project_eq_loopify_of_subset_coloops (hX : X ⊆ M﹡.cl ∅) : M ⟋ X = M ⟍ X :=
  eq_of_cl_eq_cl_forall fun S => by
    rw [project.cl_eq, loopify.cl_eq, cl_union_eq_of_subset_coloops _ hX,
      cl_diff_eq_of_subset_coloops _ hX, diff_union_self]

theorem project_eq_loopify_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X := by
  rw [project_eq_self_iff_subset_loops.mpr hX, loopify_eq_self_iff_subset_loops.mpr hX]

theorem Loop.project_eq_loopify (he : M.Loop e) : M ⟋ e = M ⟍ e :=
  project_eq_loopify_of_subset_loops (singleton_subset_iff.mpr he)

theorem Coloop.project_eq_loopify (he : M.Coloop e) : M ⟋ e = M ⟍ e :=
  project_eq_loopify_of_subset_coloops (singleton_subset_iff.mpr he)

end Project

section Pseudominor

theorem project_loopify_swap (M : Matroid E) (C D : Set E) : M ⟋ C ⟍ D = M ⟍ (D \ C) ⟋ C :=
  by
  refine' eq_of_cl_eq_cl_forall fun X => _
  simp only [project.cl_eq, loopify.cl_eq]
  rw [union_diff_distrib, sdiff_sdiff_cancel_right, @diff_eq_compl_inter _ D C,
    @diff_eq_compl_inter _ X (Cᶜ ∩ D), compl_inter, compl_compl, inter_distrib_right,
    union_right_comm, union_eq_right_iff_subset.mpr (inter_subset_left _ _), ← diff_eq_compl_inter,
    union_comm C, union_eq_union_iff_left]
  refine' ⟨_, (inter_subset_right _ _).trans (subset_union_right _ _)⟩
  rw [← diff_eq_compl_inter]
  nth_rw 1 [← inter_union_diff D C]
  refine'
    union_subset ((inter_subset_right _ _).trans (subset_union_of_subset_left _ _))
      (subset_union_right _ _)
  exact (subset_union_right _ _).trans (M.subset_cl _)

@[simp]
theorem loopify_project_swap (M : Matroid E) (C D : Set E) : M ⟍ D ⟋ C = M ⟋ (C \ D) ⟍ D :=
  by
  rw [project_loopify_swap, sdiff_sdiff_cancel_right]
  nth_rw 1 [← inter_union_diff C D]
  rw [union_comm, ← project_project]
  apply project.eq_of_subset_loops
  simp only [project.cl_eq, empty_union, loopify.cl_eq, sdiff_idem]
  exact (inter_subset_right _ _).trans (subset_union_right _ _)

theorem project_loopify_comm (M : Matroid E) {C D : Set E} (hCD : Disjoint C D) :
    M ⟋ C ⟍ D = M ⟍ D ⟋ C := by
  convert project_loopify_swap _ _ _
  rwa [eq_comm, sdiff_eq_left, disjoint_comm]

theorem project_lrestr_eq_project_lrestr_diff (M : Matroid E) (C R : Set E) :
    M ⟋ C ‖ R = M ⟋ C ‖ (R \ C) :=
  by
  rw [lrestr_eq_lrestr_of_subset_of_diff_loops (diff_subset _ _)]
  simp only [sdiff_sdiff_right_self, inf_eq_inter, project_loops_eq]
  exact (inter_subset_right _ _).trans (subset_cl _ _)

theorem lrestr_project_eq_lrestr_project_inter (M : Matroid E) (R C : Set E) :
    M ‖ R ⟋ C = M ‖ R ⟋ (C ∩ R) :=
  by
  nth_rw 1 [← inter_union_diff C R]
  rw [← project_project, project_eq_self_iff_subset_loops, project_loops_eq, lrestr.cl_eq]
  refine' subset_union_of_subset_right _ _
  rw [diff_subset_iff, union_compl_self]
  exact subset_univ C

theorem project_lrestr_eq_lrestr_project (M : Matroid E) (C R : Set E) :
    M ⟋ C ‖ R = M ‖ (R ∪ C) ⟋ C :=
  by
  refine' eq_of_cl_eq_cl_forall fun X => _
  simp only [lrestr.cl_eq, project.cl_eq, compl_union]
  rw [← union_distrib_right, union_distrib_left, eq_comm, inter_eq_left_iff_subset,
    union_subset_iff, and_iff_right (subset_union_left _ _), compl_subset_comm, compl_union,
    compl_compl, disjoint_iff_inter_eq_empty.mp]
  · apply empty_subset
  rw [disjoint_compl_left_iff_subset]
  exact M.subset_cl_of_subset (subset_union_right _ _)

theorem lrestr_project_eq_project_lrestr (M : Matroid E) (C R : Set E) :
    M ‖ R ⟋ C = M ⟋ (R ∩ C) ‖ (R \ C) := by
  rw [project_lrestr_eq_lrestr_project, union_comm, inter_union_diff,
    lrestr_project_eq_lrestr_project_inter, inter_comm]

theorem project_loopify_eq_self_iff_subset_loops : M ⟋ C ⟍ D = M ↔ C ∪ D ⊆ M.cl ∅ :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← h]
    simp only [loopify.cl_eq, empty_diff, project.cl_eq, empty_union, union_subset_iff,
      subset_union_right, and_true_iff]
    exact subset_union_of_subset_left (M.subset_cl _) _
  rw [loopify_eq_self_iff_subset_loops.mpr, project_eq_self_iff_subset_loops.mpr]
  · exact (subset_union_left _ _).trans h
  simp only [project.cl_eq, empty_union]
  exact (subset_union_right _ _).trans (h.trans (M.cl_mono (empty_subset C)))

/-- a pminor (pseudominor) of a matroid M is a matroid on the same ground set arising
-- from loopifications and/or projections of M  -/
def Pminor (N M : Matroid E) : Prop :=
  ∃ C D : Set E, N = M ⟋ C ⟍ D

def StrictPminor (N M : Matroid E) : Prop :=
  Pminor N M ∧ N ≠ M

-- mathport name: «expr ≤p »
infixl:75 " ≤p " => Matroid.Pminor

-- mathport name: «expr <p »
infixl:75 " <p " => Matroid.StrictPminor

theorem StrictPminor.pminor (h : N <p M) : N ≤p M :=
  h.1

theorem StrictPminor.ne (h : N <p M) : N ≠ M :=
  h.2

theorem Pminor.strictPminor_of_ne (h : N ≤p M) (hne : N ≠ M) : N <p M :=
  ⟨h, hne⟩

theorem Pminor.weakImage (h : N ≤p M) : N ≤w M :=
  by
  obtain ⟨C, D, rfl⟩ := h
  exact trans_of (· ≤w ·) (loopify.weak_image _ _) (project_weak_image _ _)

theorem RFin.pminor (h : M.RFin X) (hNM : N ≤p M) : N.RFin X :=
  h.WeakImage hNM.WeakImage

theorem Pminor.finiteRk [FiniteRk M] (h : N ≤p M) : FiniteRk N :=
  h.WeakImage.FiniteRk

theorem project_pminor (M : Matroid E) (C : Set E) : M ⟋ C ≤p M :=
  ⟨C, ∅, by simp⟩

theorem loopify_pminor (M : Matroid E) (D : Set E) : M ⟍ D ≤p M :=
  ⟨∅, D, by simp⟩

theorem project_loopify_pminor (M : Matroid E) (C D : Set E) : M ⟋ C ⟍ D ≤p M :=
  ⟨C, D, rfl⟩

theorem loopify_project_pminor (M : Matroid E) (C D : Set E) : M ⟍ D ⟋ C ≤p M :=
  ⟨C \ D, D, by rw [loopify_project_swap]⟩

theorem pminor_iff_project_restr : N ≤p M ↔ ∃ C R : Set E, N = M ⟋ C ‖ R :=
  by
  constructor
  · rintro ⟨C, D, rfl⟩
    refine' ⟨C, Dᶜ, _⟩
    rw [loopify_eq_lrestr_compl]
  rintro ⟨C, R, rfl⟩; refine' ⟨C, Rᶜ, _⟩; rw [loopify_eq_lrestr_compl, compl_compl]

theorem exists_canonical_pminor_of_pminor (h : N ≤p M) :
    ∃ C D, N = M ⟋ C ⟍ D ∧ M.indep C ∧ Disjoint D (M.cl C) :=
  by
  obtain ⟨C', D', rfl⟩ := h
  obtain ⟨C, hC⟩ := M.exists_basis C'
  refine' ⟨C, D' \ M.cl C, _, hC.indep, disjoint_sdiff_left⟩
  nth_rw 1 [← inter_union_diff D' (M.cl C)]
  rw [hC.project_eq_project, union_comm, ← loopify_loopify, loopify_eq_self_iff_subset_loops,
    loopify.cl_eq, empty_diff, project.cl_eq, empty_union, hC.cl]
  exact (inter_subset_right _ _).trans (subset_union_left _ _)

instance {E : Type _} : IsPartialOrder (Matroid E) (· ≤p ·)
    where
  refl _ := ⟨∅, ∅, by simp⟩
  trans := by
    intro M M' M'' h h'
    rw [pminor_iff_project_restr] at h h'⊢
    obtain ⟨C₁, R₁, rfl⟩ := h'
    obtain ⟨C₀, R₀, rfl⟩ := h
    simp only [lrestr_project_eq_project_lrestr, project_project, lrestr_lrestr]
    exact ⟨_, _, rfl⟩
  antisymm _ _ h h' := antisymm_of (· ≤w ·) h.WeakImage h'.WeakImage

theorem Pminor.eq_of_loops_subset_loops (h : N ≤p M) (h_loops : N.cl ∅ ⊆ M.cl ∅) : N = M :=
  by
  obtain ⟨C, D, rfl⟩ := h
  rw [project_loopify_eq_self_iff_subset_loops]
  simp only [loopify.cl_eq, project.cl_eq, empty_diff, empty_union] at *
  exact (union_subset_union_left D (M.subset_cl C)).trans h_loops

theorem strictPminor_of_project_nonloop (he : ¬M.Loop e) : M ⟋ e <p M :=
  by
  refine' (project_pminor M {e}).strictPminor_of_ne fun h => he _
  rwa [project_eq_self_iff_subset_loops, singleton_subset_iff, ← loop_iff_mem_cl_empty] at h

theorem strictPminor_of_loopify_nonloop (he : ¬M.Loop e) : M ⟍ e <p M :=
  by
  refine' (loopify_pminor M {e}).strictPminor_of_ne fun h => he _
  rwa [loopify_eq_self_iff_subset_loops, singleton_subset_iff, ← loop_iff_mem_cl_empty] at h

/-
lemma strict_pminor_of_project_loopify_r_ne_zero [finite_rk M] (h : M.r (C ∪ D) ≠ 0) :
  M ⟋ C ⟍ D < M :=
begin
  refine (project_loopify_pminor _ _ _).strict_pminor_of_ne
    (λ hC, h (r_eq_zero_iff_subset_loops.mpr _)),
  rwa [project_loopify_eq_self_iff_subset_loops] at hC,
end

lemma strict_pminor_of_project_r_ne_zero [finite_rk M] (h : M.r (C) ≠ 0) : M ⟋ C < M :=
begin
  refine (project_pminor _ _).strict_pminor_of_ne (λ hC, h (r_eq_zero_iff_subset_loops.mpr _)),
  rwa [project_eq_self_iff_subset_loops] at hC,
end
-/
theorem Pminor.loops_supset_loops (h : N ≤p M) : M.cl ∅ ⊆ N.cl ∅ :=
  by
  obtain ⟨C, D, rfl⟩ := h
  simp only [loopify.cl_eq, empty_diff, project.cl_eq, empty_union]
  exact subset_union_of_subset_left (M.cl_mono (empty_subset C)) _

theorem Pminor.nonloops_subset_nonloops (h : N ≤p M) : N.nonloops ⊆ M.nonloops :=
  by
  simp_rw [nonloops_eq_compl_cl_empty, compl_subset_compl]
  exact h.loops_supset_loops

theorem StrictPminor.nonloops_sSubset_nonloops (h : N <p M) : N.nonloops ⊂ M.nonloops :=
  by
  refine' h.pminor.nonloops_subset_nonloops.ssubset_of_ne fun he => h.ne _
  rw [nonloops_eq_compl_cl_empty, nonloops_eq_compl_cl_empty, compl_inj_iff] at he
  exact h.pminor.eq_of_loops_subset_loops he.subset

end Pseudominor

end Matroid

