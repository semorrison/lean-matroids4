import Matroid.MatroidIn.Basic

open Classical

noncomputable section

open Matroid Set

variable {E α : Type _}

namespace MatroidIn

section ConDel

variable {I J C D B X Y Z R : Set α} {M : MatroidIn α}

/-- Contract a set from a `matroid_in α` to give a smaller `matroid_in α`-/
def contract (M : MatroidIn α) (C : Set α) : MatroidIn α
    where
  ground := M.e \ C
  carrier := (M : Matroid α) ⟋ C
  support :=
    by
    simp only [project.cl_eq, empty_union, diff_eq_compl_inter, compl_inter, compl_compl]
    exact
      union_subset (M.carrier.subset_cl C) (M.support.trans (M.carrier.cl_mono (empty_subset _)))

/-- Restrict a `matroid_in α` to a smaller ground set. -/
def restrict (M : MatroidIn α) (R : Set α) : MatroidIn α :=
  ⟨M.e ∩ R, M ‖ R, by
    rw [lrestr.cl_eq, empty_inter, compl_inter]
    exact union_subset_union_left _ (compl_ground_subset_loops_coe _)⟩

def delete (M : MatroidIn α) (D : Set α) : MatroidIn α :=
  M.restrict (Dᶜ)

instance {α : Type _} : HasCon (MatroidIn α) (Set α) :=
  ⟨MatroidIn.contract⟩

instance {α : Type _} : HasDel (MatroidIn α) (Set α) :=
  ⟨MatroidIn.delete⟩

instance {α : Type _} : HasRestr (MatroidIn α) (Set α) :=
  ⟨MatroidIn.restrict⟩

instance {α : Type _} : HasCon (MatroidIn α) α :=
  ⟨fun M e => M.contract {e}⟩

instance {α : Type _} : HasDel (MatroidIn α) α :=
  ⟨fun M e => M.delete {e}⟩

@[simp]
theorem contract_coe (M : MatroidIn α) (C : Set α) :
    ((M ⟋ C : MatroidIn α) : Matroid α) = (M : Matroid α) ⟋ C :=
  rfl

@[simp]
theorem contract_elem (M : MatroidIn α) (e : α) : M ⟋ e = M ⟋ ({e} : Set α) :=
  rfl

@[simp]
theorem contract_ground (M : MatroidIn α) (C : Set α) : (M ⟋ C).e = M.e \ C :=
  rfl

@[simp]
theorem delete_coe (M : MatroidIn α) (D : Set α) :
    ((M ⟍ D : MatroidIn α) : Matroid α) = (M : Matroid α) ⟍ D :=
  rfl

@[simp]
theorem restrict_coe (M : MatroidIn α) (R : Set α) :
    ((M ‖ R : MatroidIn α) : Matroid α) = (M : Matroid α) ‖ R :=
  rfl

@[simp]
theorem delete_elem (M : MatroidIn α) (e : α) : M ⟍ e = M ⟍ ({e} : Set α) :=
  rfl

@[simp]
theorem delete_ground (M : MatroidIn α) (D : Set α) : (M ⟍ D).e = M.e \ D :=
  rfl

@[simp]
theorem restrict_ground (M : MatroidIn α) (R : Set α) : (M ‖ R).e = M.e ∩ R :=
  rfl

@[simp]
theorem restrict_ground_self (M : MatroidIn α) : M ‖ M.e = M :=
  by
  refine' eq_of_coe_eq_coe (by simp) _
  rw [restrict_coe, lrestr_eq_self_iff]
  exact M.support

theorem restrict_eq_self_iff : M ‖ X = M ↔ M.e ⊆ X :=
  by
  rw [← eq_iff_coe_eq_coe, restrict_ground, inter_eq_left_iff_subset, restrict_coe,
    lrestr_eq_self_iff, compl_subset_comm, ← union_subset_iff]
  convert Iff.rfl
  rw [eq_comm, union_eq_left_iff_subset, compl_subset_comm]
  exact M.support

theorem restrict_eq_delete (M : MatroidIn α) (R : Set α) : M ‖ R = M ⟍ Rᶜ :=
  by
  change M ‖ R = M ‖ Rᶜᶜ
  rw [compl_compl]

theorem delete_eq_restrict (M : MatroidIn α) (D : Set α) : M ⟍ D = M ‖ Dᶜ :=
  rfl

@[simp]
theorem restrict_restrict (M : MatroidIn α) (R₁ R₂ : Set α) : M ‖ R₁ ‖ R₂ = M ‖ (R₁ ∩ R₂) :=
  eq_of_coe_eq_coe (by simp [inter_assoc]) (by simp)

theorem restrict_restrict_of_subset (M : MatroidIn α) {R₁ R₂ : Set α} (h : R₂ ⊆ R₁) :
    M ‖ R₁ ‖ R₂ = M ‖ R₂ := by rw [restrict_restrict, inter_eq_self_of_subset_right h]

@[simp]
theorem contract_contract (M : MatroidIn α) (C₁ C₂ : Set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ (C₁ ∪ C₂) :=
  eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

@[simp]
theorem contract_empty (M : MatroidIn α) : M ⟋ (∅ : Set α) = M :=
  eq_of_coe_eq_coe (by simp) (by simp)

@[simp]
theorem delete_empty (M : MatroidIn α) : M ⟍ (∅ : Set α) = M :=
  eq_of_coe_eq_coe (by simp) (by simp)

theorem contract_eq_self_of_disjoint_ground (hC : Disjoint C M.e) : M ⟋ C = M :=
  by
  apply eq_of_coe_eq_coe
  rw [contract_ground, hC.sdiff_eq_right]
  rw [contract_coe, project.eq_of_subset_loops]
  exact subset_loops_coe_of_disjoint_ground hC

theorem contract_eq_self_iff_disjoint_ground : M ⟋ C = M ↔ Disjoint C M.e :=
  ⟨fun hM => by
    rw [← hM]
    exact disjoint_sdiff_right, contract_eq_self_of_disjoint_ground⟩

theorem delete_eq_self_of_disjoint_ground (hD : Disjoint D M.e) : M ⟍ D = M :=
  by
  apply eq_of_coe_eq_coe
  rw [delete_ground, hD.sdiff_eq_right]
  rw [delete_coe, loopify.eq_of_subset_loops]
  exact subset_loops_coe_of_disjoint_ground hD

theorem delete_eq_self_iff_disjoint_ground : M ⟍ C = M ↔ Disjoint C M.e :=
  ⟨fun hM => by
    rw [← hM]
    exact disjoint_sdiff_right, delete_eq_self_of_disjoint_ground⟩

theorem contract_comm (M : MatroidIn α) (C₁ C₂ : Set α) : M ⟋ C₁ ⟋ C₂ = M ⟋ C₂ ⟋ C₁ := by
  rw [contract_contract, contract_contract, union_comm]

@[simp]
theorem delete_delete (M : MatroidIn α) (D₁ D₂ : Set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ (D₁ ∪ D₂) :=
  eq_of_coe_eq_coe (by simp [diff_diff]) (by simp)

theorem delete_comm (M : MatroidIn α) (D₁ D₂ : Set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₂ ⟍ D₁ := by
  rw [delete_delete, delete_delete, union_comm]

theorem delete_delete_diff (M : MatroidIn α) (D₁ D₂ : Set α) : M ⟍ D₁ ⟍ D₂ = M ⟍ D₁ ⟍ (D₂ \ D₁) :=
  by
  nth_rw 1 [← inter_union_diff D₂ D₁]
  rw [union_comm, ← delete_delete, delete_eq_self_iff_disjoint_ground]
  exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) disjoint_sdiff_right

theorem restrict_eq_restrict_inter_ground (M : MatroidIn α) (R : Set α) : M ‖ R = M ‖ (R ∩ M.e) :=
  by
  rw [restrict_eq_delete, restrict_eq_delete, compl_inter, ← delete_delete, eq_comm,
    delete_eq_self_of_disjoint_ground]
  exact disjoint_of_subset_right (diff_subset _ _) disjoint_compl_left

theorem restrict_eq_delete_diff (M : MatroidIn α) (R : Set α) : M ‖ R = M ⟍ (M.e \ R) :=
  by
  rw [restrict_eq_delete]
  nth_rw 1 [← inter_union_diff (Rᶜ) M.E]
  rw [← diff_eq_compl_inter, ← delete_delete, delete_eq_self_iff_disjoint_ground]
  exact disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left

theorem contract_contract_diff (M : MatroidIn α) (C₁ C₂ : Set α) :
    M ⟋ C₁ ⟋ C₂ = M ⟋ C₁ ⟋ (C₂ \ C₁) :=
  by
  nth_rw 1 [← inter_union_diff C₂ C₁]
  rw [union_comm, ← contract_contract, contract_eq_self_iff_disjoint_ground]
  exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) disjoint_sdiff_right

theorem contract_delete_diff (M : MatroidIn α) (C D : Set α) : M ⟋ C ⟍ D = M ⟋ C ⟍ (D \ C) :=
  by
  nth_rw 1 [← inter_union_diff D C]
  rw [union_comm, ← delete_delete, delete_eq_self_iff_disjoint_ground]
  exact disjoint_of_subset (inter_subset_right _ _) (diff_subset _ _) disjoint_sdiff_right

theorem contract_delete_comm (M : MatroidIn α) {C D : Set α} (hCD : Disjoint C D) :
    M ⟋ C ⟍ D = M ⟍ D ⟋ C :=
  eq_of_coe_eq_coe (by simp [diff_diff_comm]) (by simp [project_loopify_comm _ hCD])

theorem contract_indep_iff (hI : M.indep I) : (M ⟋ I).indep X ↔ M.indep (X ∪ I) ∧ X ⊆ M.e \ I :=
  by
  rw [indep_iff_coe, contract_coe, hI.project_indep_iff, and_comm', indep_iff_coe, subset_diff] at *
  exact
    ⟨fun h => ⟨h.1, indep.subset_ground (h.1.Subset (subset_union_left _ _)), h.2⟩, fun h =>
      ⟨h.1, h.2.2⟩⟩

theorem Indep.of_contract (hI : (M ⟋ C).indep I) : M.indep I :=
  hI.of_project

@[simp]
theorem restrict_indep_iff : (M ‖ R).indep I ↔ M.indep I ∧ I ⊆ R := by
  rw [indep_iff_coe, restrict_coe, lrestr.indep_iff, ← indep_iff_coe]

theorem Indep.of_restrict (h : (M ‖ R).indep I) : M.indep I :=
  (restrict_indep_iff.mp h).1

@[simp]
theorem delete_indep_iff : (M ⟍ D).indep I ↔ M.indep I ∧ Disjoint I D := by
  rw [indep_iff_coe, delete_coe, loopify.indep_iff, and_comm', indep_iff_coe]

@[simp]
theorem delete_circuit_iff : (M ⟍ D).Circuit C ↔ M.Circuit C ∧ Disjoint C D :=
  by
  obtain h | h := em (Disjoint C D)
  · simp_rw [circuit, delete_coe, loopify.circuit_iff_of_disjoint h, iff_true_intro h, and_true_iff]
    exact
      ⟨fun h' => ⟨h'.1, h'.2.trans (diff_subset _ _)⟩, fun h' => ⟨h'.1, subset_diff.mpr ⟨h'.2, h⟩⟩⟩
  rw [circuit, delete_ground, subset_diff]
  simp [h]

theorem Indep.delete_indep (hI : M.indep I) (hID : Disjoint I D) : (M ⟍ D).indep I :=
  delete_indep_iff.mpr ⟨hI, hID⟩

@[simp]
theorem contract_cl (M : MatroidIn α) (C X : Set α) : (M ⟋ C).cl X = M.cl (X ∪ C) \ C := by
  rw [cl_eq_coe_cl_inter, contract_coe, project.cl_eq, contract_ground, cl_eq_coe_cl_inter, diff_eq,
    diff_eq, inter_assoc]

@[simp]
theorem delete_cl (M : MatroidIn α) (h : Disjoint X D) : (M ⟍ D).cl X = M.cl X \ D := by
  rw [cl_eq_coe_cl_inter, cl_eq_coe_cl_inter, delete_coe, loopify.cl_eq, delete_ground,
    h.sdiff_eq_left, inter_distrib_right, inter_diff_self, union_empty, diff_eq, diff_eq,
    inter_assoc]

@[simp]
theorem restrict_cl (M : MatroidIn α) (h : X ⊆ R) : (M ‖ R).cl X = M.cl X ∩ R := by
  rw [cl, restrict_coe, restrict_ground, lrestr.cl_eq, inter_distrib_right, inter_comm (Rᶜ),
    inter_assoc, inter_compl_self, inter_empty, union_empty, inter_eq_self_of_subset_left h, cl,
    inter_assoc]

@[simp]
theorem delete_loops (M : MatroidIn α) (D : Set α) : (M ⟍ D).cl ∅ = M.cl ∅ \ D :=
  by
  rw [delete_cl]
  exact empty_disjoint _

theorem contract_eq_contract_inter_ground (M : MatroidIn α) (C : Set α) : M ⟋ C = M ⟋ (C ∩ M.e) :=
  by
  nth_rw 1 [← inter_union_diff C M.E]
  rw [← contract_contract, contract_eq_self_of_disjoint_ground]
  rw [contract_ground]
  exact disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left

theorem delete_eq_delete_inter_ground (M : MatroidIn α) (D : Set α) : M ⟍ D = M ⟍ (D ∩ M.e) :=
  by
  nth_rw 1 [← inter_union_diff D M.E]
  rw [← delete_delete, delete_eq_self_of_disjoint_ground]
  rw [delete_ground]
  exact disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left

theorem Indep.contract_indep_iff (hI : M.indep I) :
    (M ⟋ I).indep J ↔ Disjoint J I ∧ M.indep (J ∪ I) :=
  Matroid.Indep.project_indep_iff hI

theorem contract_loops (M : MatroidIn α) (C : Set α) : (M ⟋ C).cl ∅ = M.cl C \ C := by
  rw [contract_cl, empty_union]

@[simp]
theorem delete_r_eq (M : MatroidIn α) (D X : Set α) : (M ⟍ D).R X = M.R (X \ D) := by
  rw [r_eq_coe_r, r_eq_coe_r, delete_coe, loopify.r_eq]

theorem RFin.contract (h : M.RFin X) (C : Set α) : (M ⟋ C).RFin (X \ C) :=
  by
  refine' ⟨(h.to_coe.project C).Subset (diff_subset _ _), _⟩
  rw [diff_subset_iff, contract_ground, union_diff_self]
  exact subset_union_of_subset_right h.subset_ground _

theorem RFin.of_contract (h : (M ⟋ C).RFin X) (hC : M.RFin C) : M.RFin X :=
  ⟨RFin.of_project (by simpa using h.to_coe) hC.to_coe, h.subset_ground.trans (diff_subset _ _)⟩

theorem RFin.rFin_contract_iff (hC : M.RFin C) : (M ⟋ C).RFin X ↔ M.RFin X ∧ Disjoint X C :=
  by
  constructor
  exact fun h => ⟨h.of_contract hC, disjoint_of_subset_left h.subset_ground disjoint_sdiff_left⟩
  rintro ⟨hX, hXC⟩
  convert hX.contract C
  rwa [eq_comm, sdiff_eq_left]

theorem RFin.contract_r_cast_eq (h : M.RFin X) (hC : M.RFin C) :
    ((M ⟋ C).R X : ℤ) = M.R (X ∪ C) - M.R C :=
  h.to_coe.project_cast_r_eq hC.to_coe

theorem RFin.contract_r_add_r_eq (h : M.RFin X) (hC : M.RFin C) :
    (M ⟋ C).R X + M.R C = M.R (X ∪ C) := by
  zify
  simp [h.contract_r_cast_eq hC]

@[simp]
theorem contract_r_cast_eq (M : MatroidIn α) [M.FiniteRk] (X C : Set α) :
    ((M ⟋ C).R X : ℤ) = M.R (X ∪ C) - M.R C := by
  rw [r_eq_coe_r, contract_coe, project_cast_r_eq, r_eq_coe_r, r_eq_coe_r]

@[simp]
theorem contract_r_add_r_eq (M : MatroidIn α) [M.FiniteRk] (X C : Set α) :
    (M ⟋ C).R X + M.R C = M.R (X ∪ C) := by
  zify
  simp [contract_r_cast_eq]

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (Y «expr ⊆ » M.E) -/
@[simp]
theorem contract_dual (M : MatroidIn α) (X : Set α) : (M ⟋ X)﹡ = M﹡ ⟍ X :=
  by
  suffices ∀ (Y) (_ : Y ⊆ M.E), (M ⟋ Y)﹡ = M﹡ ⟍ Y
    by
    convert this (X ∩ M.E) (inter_subset_right _ _) using 1
    rw [dual_inj_iff, contract_eq_contract_inter_ground]
    rw [delete_eq_delete_inter_ground, dual_ground]
  refine' fun Y hY => eq_of_indep_iff_indep_forall rfl fun I hI => _
  rw [dual_indep_iff_coindep, delete_indep_iff, dual_indep_iff_coindep,
    coindep_iff_cl_compl_eq_ground, coindep_iff_cl_compl_eq_ground]
  · rw [dual_ground, contract_ground] at hI
    have hXI := disjoint_of_subset_left hI disjoint_sdiff_left
    rw [iff_true_intro hXI, and_true_iff, contract_ground, contract_cl, diff_diff,
      subset_antisymm_iff, diff_subset_iff, union_diff_self, diff_subset_iff, union_diff_self,
      iff_true_intro (subset_union_of_subset_right (cl_subset_ground _ _) _), true_and_iff,
      union_eq_self_of_subset_left ((subset_cl hY).trans (cl_subset _ (subset_union_right _ _))),
      diff_eq, union_distrib_right, union_eq_self_of_subset_right hY, compl_union,
      union_distrib_right, compl_union_self, univ_inter, inter_distrib_left,
      union_eq_self_of_subset_right, ← diff_eq, subset_antisymm_iff,
      iff_true_intro (cl_subset_ground _ _), true_and_iff]
    exact (inter_subset_right _ _).trans (subset_inter hY (subset_compl_iff_disjoint_left.mpr hXI))
  · refine' hI.trans _
    simp [diff_subset]
  convert hI using 1

@[simp]
theorem delete_dual (M : MatroidIn α) (X : Set α) : (M ⟍ X)﹡ = M﹡ ⟋ X := by
  rw [← dual_inj_iff, contract_dual, dual_dual, dual_dual]

@[simp]
theorem contract_coindep_iff : (M ⟋ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [← dual_indep_iff_coindep, contract_dual, delete_indep_iff, dual_indep_iff_coindep]

theorem Coindep.contract_coindep (h : M.Coindep X) (hdj : Disjoint X C) : (M ⟋ C).Coindep X :=
  contract_coindep_iff.mpr ⟨h, hdj⟩

theorem contract_eq_delete_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⟋ X = M ⟍ X :=
  by
  refine' eq_of_indep_iff_indep_forall rfl fun I (hI : I ⊆ M.E \ X) => _
  rw [subset_diff] at hI
  rw [delete_indep_iff, indep_iff_coe, contract_coe, ← (true_iff_iff _).mpr hI.2, and_true_iff,
    project.eq_of_subset_loops (hX.trans (cl_subset_coe_cl _ _)), indep_iff_coe]

theorem contract_eq_delete_of_subset_coloops (M : MatroidIn α) {X : Set α} (hX : X ⊆ M﹡.cl ∅) :
    M ⟋ X = M ⟍ X := by
  rw [← dual_inj_iff, contract_dual, delete_dual, contract_eq_delete_of_subset_loops hX]

theorem contract_cl_eq_contract_delete (M : MatroidIn α) (C : Set α) :
    M ⟋ M.cl C = M ⟋ C ⟍ (M.cl C \ C) :=
  by
  rw [← contract_eq_delete_of_subset_loops, contract_contract, union_diff_self, union_comm, ←
    union_diff_self, ← contract_contract, eq_comm]
  refine' contract_eq_self_of_disjoint_ground _
  · rw [contract_ground, cl_eq_coe_cl_inter, diff_inter,
      diff_eq_empty.mpr (Matroid.subset_cl (M : Matroid α) _), empty_union]
    exact disjoint_of_subset_right (diff_subset _ _) disjoint_sdiff_left
  rw [contract_cl, empty_union]

theorem Basis.contract_eq (h : M.Basis I X) : M ⟋ X = M ⟋ I ⟍ (X \ I) :=
  by
  nth_rw 1 [← union_diff_cancel h.subset]
  rw [← contract_contract, contract_eq_delete_of_subset_loops]
  rw [contract_cl, empty_union]
  exact diff_subset_diff_left h.subset_cl

@[simp]
theorem restrict_contract_eq_contract_restrict (M : MatroidIn α) (R C : Set α) :
    M ‖ R ⟋ C = M ⟋ (R ∩ C) ‖ (R \ C) :=
  by
  refine' eq_of_coe_eq_coe _ (lrestr_project_eq_project_lrestr _ _ _)
  ext
  simp only [contract_ground, restrict_ground, mem_diff, mem_inter_iff, not_and]
  tauto

theorem restrict_contract_eq_contract_restrict_of_subset (M : MatroidIn α) (h : C ⊆ R) :
    M ‖ R ⟋ C = M ⟋ C ‖ (R \ C) := by
  rw [restrict_contract_eq_contract_restrict, inter_eq_self_of_subset_right h]

theorem restrict_contract_eq_restrict_contract_inter (M : MatroidIn α) (R C : Set α) :
    M ‖ R ⟋ C = M ‖ R ⟋ (C ∩ R) :=
  by
  refine' eq_of_coe_eq_coe _ (lrestr_project_eq_lrestr_project_inter _ _ _)
  ext
  simp only [restrict_contract_eq_contract_restrict, restrict_ground, contract_ground,
    mem_inter_iff, mem_diff, not_and, diff_inter_self_eq_diff]
  tauto

theorem contract_restrict_eq_restrict_contract (M : MatroidIn α) (R C : Set α) :
    M ⟋ C ‖ R = M ‖ (R ∪ C) ⟋ C :=
  by
  refine' eq_of_coe_eq_coe _ (project_lrestr_eq_lrestr_project _ _ _)
  ext;
  simp only [restrict_ground, contract_ground, mem_inter_iff, mem_diff, union_diff_right, mem_union]
  tauto

theorem contract_restrict_eq_contract_restr_diff (M : MatroidIn α) (R C : Set α) :
    M ⟋ C ‖ R = M ⟋ C ‖ (R \ C) :=
  by
  refine' eq_of_coe_eq_coe _ (project_lrestr_eq_project_lrestr_diff _ _ _)
  ext
  simp only [restrict_ground, contract_ground, mem_inter_iff, mem_diff, and_congr_right_iff]
  tauto

-- ### Skewness and minors
theorem contract_restrict_eq_restrict_iff_skew_coe (hCR : Disjoint C R) :
    M ⟋ C ‖ R = M ‖ R ↔ (M : Matroid α).Skew C R :=
  by
  rw [Matroid.Skew, ← eq_iff_coe_eq_coe]
  simp only [restrict_ground, contract_ground, restrict_coe, contract_coe, and_iff_right_iff_imp]
  rintro -
  rw [diff_eq, inter_right_comm, inter_eq_left_iff_subset, subset_compl_iff_disjoint_left]
  exact disjoint_of_subset_right (inter_subset_right _ _) hCR

theorem skew_iff_contract_restrict_eq_restrict (hC : C ⊆ M.e) (hR : R ⊆ M.e) (hCR : Disjoint C R) :
    M.Skew C R ↔ M ⟋ C ‖ R = M ‖ R :=
  by
  rw [contract_restrict_eq_restrict_iff_skew_coe hCR]
  exact ⟨skew.to_coe, fun h => ⟨h, hC, hR⟩⟩

theorem skew_of_indep_contract (hC : C ⊆ M.e) (hI : (M ⟋ C).indep I) : M.Skew I C :=
  by
  rw [skew.comm]
  simp_rw [skew, Matroid.Skew, and_iff_right hC,
    and_iff_left (hI.subset_ground.trans (diff_subset _ _)), lrestr_eq_lrestr_iff, ← contract_coe, ←
    indep_iff_coe]
  refine' fun J hJI => _
  rw [iff_true_intro (hI.subset hJI), true_iff_iff]
  exact hI.of_contract.subset hJI

theorem contract_skew_of_skew (hXC : Disjoint X C) (hYC : Disjoint Y C) (h : M.Skew X (Y ∪ C)) :
    (M ⟋ C).Skew X Y :=
  by
  rw [skew.comm, skew, contract_ground, subset_diff, and_iff_left hYC, subset_diff,
    and_iff_left hXC, and_iff_left h.left_subset_ground,
    and_iff_left ((subset_union_left _ _).trans h.right_subset_ground)]
  refine' project_skew_of_union_skew _
  rw [union_comm, Matroid.Skew.comm]
  exact h.to_coe

-- lemma disjoint_contract_of_eq_contract_restr {M₀ : matroid_in α} (h : M₀ = (M ⟋ C) ‖ M₀.E) :
--   disjoint M₀.E C :=
-- begin
--   rw [h, restrict_ground, contract_ground, inter_comm, diff_eq, ←inter_assoc, ←diff_eq],
--   exact disjoint_sdiff_left,
-- end
-- lemma subset_ground_of_eq_contract_restr {M₁ : }
end ConDel

section Restriction

variable {M₀ M : MatroidIn α}

/-- M₀ is a `restriction` of `M` if `M₀ = M ‖ M₀.E`. We write `M₀ ≤r M`. -/
def Restriction (M₀ M : MatroidIn α) :=
  M₀ = M ‖ M₀.e

-- mathport name: «expr ≤r »
infixl:50 " ≤r " => Restriction

theorem Restriction.left_eq (h : M₀ ≤r M) : M₀ = M ‖ M₀.e :=
  h

theorem Restriction.subset (h : M₀ ≤r M) : M₀.e ⊆ M.e :=
  by
  rw [h.left_eq, restrict_ground]
  apply inter_subset_left

@[simp]
theorem Restriction.refl (M : MatroidIn α) : M ≤r M := by simp [restriction]

theorem Restriction.trans ⦃M₀ M₁ M₂ : MatroidIn α⦄ (h₀ : M₀ ≤r M₁) (h₁ : M₁ ≤r M₂) : M₀ ≤r M₂ := by
  rw [h₀.left_eq, h₁.left_eq, restrict_restrict, restriction, restrict_ground,
    inter_eq_self_of_subset_right ((inter_subset_left _ _).trans h₁.subset)]

theorem Restriction.antisymm ⦃M₁ M₂ : MatroidIn α⦄ (h₁ : M₁ ≤r M₂) (h₂ : M₂ ≤r M₁) : M₁ = M₂ := by
  rw [h₁.left_eq, h₂.left_eq, restrict_restrict_of_subset _ h₁.subset, h₁.subset.antisymm h₂.subset]

/-- `≤r` is a partial order on `matroid_in α` -/
instance {α : Type _} : IsPartialOrder (MatroidIn α) (· ≤r ·)
    where
  refl := Restriction.refl
  trans := Restriction.trans
  antisymm := Restriction.antisymm

@[simp]
theorem restrict_restriction (M : MatroidIn α) (R : Set α) : M ‖ R ≤r M := by
  rw [restriction, restrict_ground, restrict_eq_restrict_inter_ground, inter_comm]

@[simp]
theorem delete_restriction (M : MatroidIn α) (D : Set α) : M ⟍ D ≤r M :=
  by
  rw [delete_eq_restrict]
  apply restrict_restriction

theorem Restriction.indep_of_indep {I : Set α} (h : M₀ ≤r M) (hI : M₀.indep I) : M.indep I :=
  by
  rw [h.left_eq] at hI
  exact hI.of_restrict

theorem ground_disjoint_of_restriction_contract {C : Set α} (h : M₀ ≤r M ⟋ C) : Disjoint M₀.e C :=
  by
  rw [h.left_eq, restrict_ground, contract_ground]
  exact disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left

end Restriction

section Minor

variable {M M₀ M₁ M₂ : MatroidIn α} {C D I R X Y Z : Set α}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (C «expr ⊆ » M.E) -/
/-- The minor order on `matroid_in α`; we write `M₀ ≤ M` if `M₀ = M ⟋ C ⟍ D` where `C,D` are
  disjoint subsets of `M.E` -/
instance {α : Type _} : PartialOrder (MatroidIn α)
    where
  le M₀ M := ∃ (C : _)(_ : C ⊆ M.e), M₀ ≤r M ⟋ C
  le_refl M := ⟨∅, by simp⟩
  le_trans := by
    rintro M₀ M₁ M₂ ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
    rw [h₂.left_eq, restrict_contract_eq_contract_restrict, contract_contract] at h₁
    exact
      ⟨_, union_subset hC₂ ((inter_subset_left _ _).trans (h₂.subset.trans (diff_subset _ _))),
        h₁.trans (restrict_restriction _ _)⟩
  le_antisymm := by
    rintro M₁ M₂ ⟨C₁, hC₁, h₁⟩ ⟨C₂, hC₂, h₂⟩
    have h₂' : C₂ = ∅ :=
      by
      have con := h₁.subset.trans ((diff_subset _ _).trans h₂.subset)
      rwa [contract_ground, subset_diff, and_iff_right subset.rfl, disjoint_comm,
        disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_left hC₂] at con
    rw [h₂', contract_empty] at h₂
    have h₁' : C₁ = ∅ := by
      have con := (h₂.trans h₁).Subset
      rwa [contract_ground, subset_diff, and_iff_right subset.rfl, disjoint_comm,
        disjoint_iff_inter_eq_empty, inter_eq_self_of_subset_left hC₁] at con
    rw [h₁', contract_empty] at h₁
    exact h₁.antisymm h₂

@[simp]
theorem Restriction.minor (h : M₀ ≤r M) : M₀ ≤ M :=
  ⟨∅, by simpa⟩

@[simp]
theorem contract_minor (M : MatroidIn α) : M ⟋ C ≤ M :=
  by
  refine' ⟨C ∩ M.E, inter_subset_right _ _, _⟩
  rw [contract_eq_contract_inter_ground]
  exact restriction.refl _

@[simp]
theorem restrict_minor (M : MatroidIn α) (R : Set α) : M ‖ R ≤ M :=
  (restrict_restriction _ _).minor

@[simp]
theorem delete_minor (M : MatroidIn α) : M ⟍ D ≤ M :=
  (delete_restriction _ _).minor

@[simp]
theorem contract_restrict_minor (M : MatroidIn α) (C R : Set α) : M ⟋ C ‖ R ≤ M :=
  (restrict_restriction _ _).minor.trans (contract_minor _)

/-- Contracting and deleting any set gives a minor, even if the contractions and deletions are
  not well-defined (i.e. they overlap or are not contained in the ground set) -/
@[simp]
theorem contract_delete_minor (M : MatroidIn α) (C D : Set α) : M ⟋ C ⟍ D ≤ M :=
  (delete_restriction _ _).minor.trans (contract_minor _)

theorem Minor.ground_subset (h : M₀ ≤ M) : M₀.e ⊆ M.e :=
  by
  obtain ⟨C, hC, h⟩ := h
  exact h.subset.trans (diff_subset _ _)

/-- Every minor is obtained by contracting an independent set and then restricting -/
theorem exists_indep_contr_of_minor (h : M₀ ≤ M) : ∃ I, M.indep I ∧ M₀ ≤r M ⟋ I :=
  by
  obtain ⟨C, hC, h⟩ := h
  obtain ⟨I, hI⟩ := M.exists_basis hC
  rw [hI.contract_eq] at h
  exact ⟨I, hI.indep, h.trans (delete_restriction _ _)⟩

theorem Minor.exists_indep_contract_spanning_restriction (h : M₀ ≤ M) :
    ∃ I : Set α, M.indep I ∧ Disjoint I M₀.e ∧ (M ⟋ I).cl M₀.e = (M ⟋ I).e ∧ M₀ ≤r M ⟋ I :=
  by
  have h₀ := minor.ground_subset h
  obtain ⟨I, hI, hr⟩ := exists_indep_contr_of_minor h
  obtain ⟨B₀, hB₀⟩ := M₀.exists_base
  have hB₀i := hr.indep_of_indep hB₀.indep
  have hsk := skew_of_indep_contract hI.subset_ground (hr.indep_of_indep hB₀.indep)
  have hdj := hsk.disjoint_of_indep_right hI
  have hB₀I := hsk.union_indep hB₀i.of_contract hI
  obtain ⟨B, hB, hssB⟩ := hB₀I.exists_base_supset
  have hdj' : Disjoint (B \ B₀) M₀.E :=
    by
    rw [disjoint_iff_inter_eq_empty, ← inter_eq_self_of_subset_right hr.subset, contract_ground,
      diff_eq M.E, inter_right_comm, inter_eq_self_of_subset_right h₀, ← diff_eq,
      eq_empty_iff_forall_not_mem]
    simp_rw [mem_inter_iff, not_and]
    rintro e ⟨heB, heB₀⟩ ⟨heM₀, heI⟩
    refine' hB₀.insert_dep heB₀ _
    rw [hr.left_eq, restrict_indep_iff, contract_indep_iff hI, subset_diff, and_comm' (_ ⊆ _),
      and_assoc', and_assoc', ← subset_inter_iff, inter_eq_self_of_subset_right h₀, insert_subset,
      and_iff_right heM₀, and_iff_left hB₀.subset_ground, ← union_singleton, disjoint_union_left,
      disjoint_singleton_left, and_iff_right (hsk.disjoint_of_indep_right hI), and_iff_left heI,
      union_singleton, insert_union]
    exact hB.indep.subset (insert_subset.mpr ⟨heB, hssB⟩)
  refine' ⟨B \ B₀, hB.indep.diff _, hdj', _, _⟩
  · simp only [contract_cl, contract_ground]
    refine' (diff_subset_diff_left (M.cl_subset_ground _)).antisymm _
    rw [diff_subset_iff,
      union_diff_cancel
        (subset_cl_of_subset ((diff_subset _ _).trans hB.subset_ground) (subset_union_right _ _)),
      union_diff_cancel_of_subset _ hB₀.subset_ground, ← cl_union_cl_right_eq_cl, hB.cl,
      union_eq_self_of_subset_left h₀]
    exact subset_cl subset.rfl
  rw [restriction]
  nth_rw 1 [hr.left_eq]
  rw [← union_diff_cancel (subset_diff.mpr ⟨(subset_union_right _ _).trans hssB, hdj.symm⟩), ←
    contract_contract, diff_diff, eq_comm, ← skew_iff_contract_restrict_eq_restrict _ hr.subset]
  · apply contract_skew_of_skew _ _ _
    · exact disjoint_of_subset_right (subset_union_right _ _) disjoint_sdiff_left
    · exact ground_disjoint_of_restriction_contract hr
    have hcl : M₀.E ∪ I ⊆ M.cl (B₀ ∪ I) :=
      by
      rintro e (he | heI)
      · have h' := hB₀.cl.symm.subset he
        rw [hr.left_eq, restrict_cl _ hB₀.subset_ground, contract_cl, diff_eq, inter_assoc] at h'
        exact h'.1
      exact (M.cl_subset (subset_union_right _ _)) (subset_cl hI.subset_ground heI)
    exact (hB.indep.skew_diff_of_subset hssB).symm.cl_right.subset_right hcl
  · exact disjoint_of_subset_left (diff_subset_diff_right (subset_union_left _ _)) hdj'
  rw [diff_subset_iff, contract_ground, union_assoc, union_diff_self, ← union_assoc]
  exact subset_union_of_subset_right hB.subset_ground _

/-- The scum theorem : every minor is obtained by contracting an independent set and deleting a
  coindependent set -/
theorem scum (h : M₀ ≤ M) :
    ∃ I X : Set α, M ⟋ I ⟍ X = M₀ ∧ M.indep I ∧ M.Coindep X ∧ Disjoint I X :=
  by
  obtain ⟨I, hI, hIM₀, hE, hle⟩ := minor.exists_indep_contract_spanning_restriction h
  have h₀ := minor.ground_subset h
  refine' ⟨I, (M.E \ I) \ M₀.E, _, hI, _, _⟩
  · nth_rw 2 [hle.left_eq]
    rw [delete_eq_restrict, restrict_eq_restrict_inter_ground]
    convert rfl
    rw [contract_ground, diff_eq, diff_eq, compl_inter, compl_inter, compl_compl, compl_compl,
      inter_distrib_right, ← inter_assoc, ← inter_assoc, inter_eq_self_of_subset_left h₀,
      inter_distrib_right, compl_inter_self, empty_union, inter_right_comm, inter_compl_self,
      empty_inter, empty_union, ← diff_eq, eq_comm, sdiff_eq_left]
    exact ground_disjoint_of_restriction_contract hle
  · rw [coindep_iff_cl_compl_eq_ground, diff_diff, sdiff_sdiff_right_self, inf_eq_inter,
      inter_distrib_left, inter_eq_self_of_subset_right h₀,
      inter_eq_self_of_subset_right hI.subset_ground, union_comm]
    · apply_fun fun X => X ∪ I  at hE
      simp only [contract_cl, diff_union_self, contract_ground] at hE
      rwa [union_eq_self_of_subset_right hI.subset_ground, union_eq_self_of_subset_right] at hE
      refine' subset_cl_of_subset hI.subset_ground (subset_union_right _ _)
    rw [diff_diff]
    exact diff_subset _ _
  rw [diff_diff]
  exact disjoint_of_subset_left (subset_union_left _ _) disjoint_sdiff_right

end Minor

section Flat

variable {M : MatroidIn α} {X Y F C : Set α} {e : α} {k : ℕ}

theorem flat_contract_iff (hC : C ⊆ M.e) : (M ⟋ C).Flat F ↔ M.Flat (F ∪ C) ∧ Disjoint F C :=
  by
  rw [flat_iff_cl_self, contract_cl, flat_iff_cl_self]
  refine' ⟨fun h => ⟨_, _⟩, fun h => _⟩
  · nth_rw 2 [← h]
    rw [diff_union_self, @union_eq_self_of_subset_right _ (M.cl _)]
    exact (subset_cl hC).trans (M.cl_subset (subset_union_right _ _))
  · rw [← h]
    exact disjoint_sdiff_left
  rw [h.1, union_diff_right, sdiff_eq_left]
  exact h.2

theorem RFin.flatOfR_contract_iff (hC : M.RFin C) :
    (M ⟋ C).FlatOfR k F ↔ M.FlatOfR (k + M.R C) (F ∪ C) ∧ Disjoint F C :=
  by
  simp_rw [flat_of_r_iff, flat_contract_iff hC.subset_ground, and_assoc', and_congr_right_iff,
    and_comm' (Disjoint _ _), ← and_assoc', and_congr_left_iff, hC.r_fin_contract_iff,
    r_fin_union_iff, and_iff_left hC, and_comm' (M.r_fin F), ← and_assoc', and_congr_left_iff]
  refine' fun hFC hdj hFC => _
  zify
  rw [and_iff_left hdj, hFC.contract_r_cast_eq hC]
  exact ⟨fun h => by rw [← h, sub_add_cancel], fun h => by rw [h, add_sub_cancel]⟩

theorem flatOfR_contract_iff [FiniteRk M] (hC : C ⊆ M.e) :
    (M ⟋ C).FlatOfR k F ↔ M.FlatOfR (k + M.R C) (F ∪ C) ∧ Disjoint F C :=
  RFin.flatOfR_contract_iff (to_rFin hC)

theorem Nonloop.point_of_contract_iff {P : Set α} (he : M.Nonloop e) :
    (M ⟋ e).Point P ↔ M.line (insert e P) ∧ e ∉ P := by
  rw [contract_elem, point, (r_fin_singleton he.mem_ground).flatOfR_contract_iff, union_singleton,
    he.r, one_add_one_eq_two, ← line, disjoint_singleton_right]

end Flat

end MatroidIn

