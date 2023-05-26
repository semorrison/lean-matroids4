import Matroid.Pseudominor

open Classical

open BigOperators

open Set

namespace Matroid

variable {E : Type _} {X Y X' Y' Z I J C : Set E} {e f : E} {M : Matroid E}

/-! Skewness -/


/-- Two sets `X,Y` are `skew` if restricting to `Y` is the same as projecting `X` and restricting
  to `Y`. For finite rank, this is the same as `r X + r Y = r (X ∪ Y)`.-/
def Skew (M : Matroid E) (X Y : Set E) : Prop :=
  M ⟋ X ‖ Y = M ‖ Y

theorem skew_iff_project_lrestr_eq_lrestr : M.Skew X Y ↔ M ⟋ X ‖ Y = M ‖ Y :=
  Iff.rfl

theorem Skew.project_lrestr_eq (h : M.Skew X Y) : M ⟋ X ‖ Y = M ‖ Y :=
  h

theorem Skew.symm (h : M.Skew X Y) : M.Skew Y X :=
  by
  rw [skew, lrestr_eq_lrestr_iff] at *
  refine' fun I hIX => ⟨fun hI => hI.of_project, fun hI => _⟩
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [hJ.project_indep_iff]
  have hi := (h J hJ.subset).mpr hJ.indep
  obtain ⟨I', hI', hIJ⟩ := hI.subset_basis_of_subset hIX
  rw [hI'.project_indep_iff, disjoint_comm, union_comm] at hi
  exact ⟨disjoint_of_subset_left hIJ hi.1, hi.2.Subset (union_subset_union_left _ hIJ)⟩

theorem Skew.comm : M.Skew X Y ↔ M.Skew Y X :=
  ⟨Skew.symm, Skew.symm⟩

theorem empty_skew (M : Matroid E) (X : Set E) : M.Skew ∅ X := by rw [skew, project_empty]

theorem skew_empty (M : Matroid E) (X : Set E) : M.Skew X ∅ := by
  rw [skew.comm, skew, project_empty]

theorem Skew.subset_right (h : M.Skew X Y) (hY'Y : Y' ⊆ Y) : M.Skew X Y' :=
  by
  rw [skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff] at h⊢
  exact fun I hI => h I (hI.trans hY'Y)

theorem Skew.subset_left (h : M.Skew X Y) (hX'X : X' ⊆ X) : M.Skew X' Y :=
  (h.symm.subset_right hX'X).symm

theorem Skew.loop_of_mem_inter (h : M.Skew X Y) (he : e ∈ X ∩ Y) : M.Loop e :=
  by
  rw [skew_iff_project_lrestr_eq_lrestr] at h
  have heY : (M ‖ Y).Loop e := by
    rw [← h, lrestr.loop_iff]
    exact Or.inl (project.loop_of_mem he.1)
  rw [lrestr.loop_iff, ← imp_iff_or_not] at heY
  exact heY he.2

theorem Skew.inter_subset_loops (h : M.Skew X Y) : X ∩ Y ⊆ M.cl ∅ := fun e => h.loop_of_mem_inter

theorem skew_of_subset_loops (h : X ⊆ M.cl ∅) (Y : Set E) : M.Skew X Y := by
  rw [skew_iff_project_lrestr_eq_lrestr, project_eq_self_iff_subset_loops.mpr h]

theorem subset_loops_skew (X : Set E) (h : Y ⊆ M.cl ∅) : M.Skew X Y :=
  (skew_of_subset_loops h X).symm

theorem Skew.diff_loops_disjoint_left (h : M.Skew X Y) : Disjoint (X \ M.cl ∅) Y :=
  by
  refine' disjoint_of_subset_left _ (@disjoint_sdiff_left _ Y X)
  rw [← @diff_inter_self_eq_diff _ X Y, inter_comm]
  exact diff_subset_diff_right h.inter_subset_loops

theorem Skew.diff_loops_disjoint_right (h : M.Skew X Y) : Disjoint X (Y \ M.cl ∅) :=
  h.symm.diff_loops_disjoint_left.symm

theorem Loop.singleton_skew (he : M.Loop e) (X : Set E) : M.Skew {e} X :=
  skew_of_subset_loops (singleton_subset_iff.mpr he) X

theorem Loop.skew_singleton (he : M.Loop e) (X : Set E) : M.Skew X {e} :=
  subset_loops_skew X (singleton_subset_iff.mpr he)

theorem Basis.skew (hI : M.Basis I X) (hJ : M.Basis J Y) (hdj : Disjoint I J)
    (hi : M.indep (I ∪ J)) : M.Skew X Y :=
  by
  rw [skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff]
  intro K hKY
  rw [hI.project_indep_iff]
  have hK' := (hKY.trans (M.subset_cl Y)).trans_eq hJ.cl.symm
  refine' ⟨fun h => h.2.Subset (subset_union_left _ _), fun h => ⟨_, _⟩⟩
  · rw [disjoint_iff_forall_ne]
    rintro e heK f heI rfl
    have heJ : e ∈ J :=
      hJ.indep.mem_cl_iff.mp (hK' heK)
        (hi.subset (insert_subset.mpr ⟨Or.inl heI, subset_union_right _ _⟩))
    exact hdj.ne_of_mem heI heJ rfl
  obtain ⟨K₁, hK₁⟩ := h.subset_basis_of_subset hKY
  obtain ⟨K₂, hK₂⟩ := hK₁.1.indep.subset_basis_of_subset (subset_union_left K₁ I)
  have hi : K₁ ∪ I = K₂ :=
    by
    refine' hK₂.1.Subset.antisymm' (union_subset hK₂.2 fun e heI => by_contra fun heK₂ => _)
    have heK₂' : e ∈ M.cl K₂ := by
      rw [hK₂.1.cl]
      exact (M.subset_cl _) (Or.inr heI)
    rw [← union_diff_cancel hK₂.2, ← cl_union_cl_left_eq_cl_union, hK₁.1.cl, ← hJ.cl,
      cl_union_cl_left_eq_cl_union] at heK₂'
    have he : e ∈ M.cl ((I ∪ J) \ {e}) :=
      by
      rw [union_comm, union_diff_distrib, diff_singleton_eq_self]
      · refine' M.cl_subset (union_subset_union_right _ _) heK₂'
        refine' subset_diff_singleton _ (not_mem_subset (diff_subset _ _) heK₂)
        exact diff_subset_iff.mpr hK₂.1.Subset
      exact fun heJ => hdj.ne_of_mem heI heJ rfl
    rw [indep_iff_not_mem_cl_diff_forall] at hi
    exact hi e (Or.inl heI) he
  subst hi
  exact hK₂.1.indep.Subset (union_subset_union_left _ hK₁.2)

theorem Skew.disjoint_of_indep_left (h : M.Skew I X) (hI : M.indep I) : Disjoint I X :=
  by
  rw [disjoint_iff_forall_ne]
  rintro e heI _ heY rfl
  exact hI.nonloop_of_mem heI (h.loop_of_mem_inter ⟨heI, heY⟩)

theorem Skew.disjoint_of_indep_right (h : M.Skew X I) (hI : M.indep I) : Disjoint X I :=
  (h.symm.disjoint_of_indep_left hI).symm

theorem Skew.union_indep (h : M.Skew I J) (hI : M.indep I) (hJ : M.indep J) : M.indep (I ∪ J) :=
  by
  rw [skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff] at h
  specialize h J subset.rfl
  rw [hI.project_indep_iff, iff_true_right hJ, union_comm] at h
  exact h.2

theorem Indep.skew_diff_of_subset (hI : M.indep I) (hJ : J ⊆ I) : M.Skew J (I \ J) :=
  by
  rw [skew.comm, skew_iff_project_lrestr_eq_lrestr, lrestr_eq_lrestr_iff]
  intro K hKJ
  rw [(hI.diff J).project_indep_iff,
    and_iff_right (disjoint_of_subset_left hKJ disjoint_sdiff_right),
    iff_true_intro (hI.subset (hKJ.trans hJ)), iff_true_iff]
  exact hI.subset (union_subset (hKJ.trans hJ) (diff_subset _ _))

theorem skew_iff_disjoint_of_union_indep (h : M.indep (I ∪ J)) : M.Skew I J ↔ Disjoint I J :=
  by
  refine'
    ⟨fun h' => disjoint_iff_inter_eq_empty.mpr ((h.subset _).eq_empty_of_subset_loops _), fun h' =>
      _⟩
  · exact inter_subset_union _ _
  · exact h'.inter_subset_loops
  convert h.skew_diff_of_subset (subset_union_left _ _)
  rwa [union_diff_left, eq_comm, sdiff_eq_left, disjoint_comm]

theorem Skew.union_indep_of_subset_of_subset (h : M.Skew X Y) (hI : M.indep I) (hIX : I ⊆ X)
    (hJ : M.indep J) (hJY : J ⊆ Y) : M.indep (I ∪ J) :=
  ((h.subset_left hIX).subset_right hJY).union_indep hI hJ

theorem Skew.inter_basis_left_of_basis_union (h : M.Skew X Y) (hI : M.Basis I (X ∪ Y)) :
    M.Basis (I ∩ X) X :=
  by
  refine' (hI.indep.inter_right X).basis_of_forall_insert (inter_subset_right _ _) fun e he hi => _
  have heY : e ∉ Y := fun heY =>
    hi.nonloop_of_mem (mem_insert e _) (h.loop_of_mem_inter ⟨he.1, heY⟩)
  rw [diff_inter, diff_self, union_empty] at he
  refine' he.2 (hI.mem_of_insert_indep (Or.inl he.1) _)
  rw [← diff_union_inter I X, union_comm, ← insert_union]
  exact
    h.union_indep_of_subset_of_subset hi (insert_subset.mpr ⟨he.1, inter_subset_right _ _⟩)
      (hI.indep.diff _) (diff_subset_iff.mpr hI.subset)

theorem Skew.inter_basis_right_of_basis_union (h : M.Skew X Y) (hI : M.Basis I (X ∪ Y)) :
    M.Basis (I ∩ Y) Y := by
  rw [union_comm] at hI
  exact h.symm.inter_basis_left_of_basis_union hI

theorem skew_iff_r [FiniteRk M] : M.Skew X Y ↔ M.R X + M.R Y = M.R (X ∪ Y) :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [skew_iff_project_lrestr_eq_lrestr] at h
    rw [← lrestr.rk_eq M Y, rk_def, ← h, lrestr.r_eq, univ_inter, add_comm,
      project.r_add_r_eq_r_union, union_comm]
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [← hI.card, ← hJ.card, ← r_union_cl_left_eq_r_union, ← hI.cl, r_union_cl_left_eq_r_union, ←
    r_union_cl_right_eq_r_union, ← hJ.cl, r_union_cl_right_eq_r_union, ←
    ncard_inter_add_ncard_union _ _ hI.finite hJ.finite] at h
  refine' hI.skew hJ _ _
  · have h' := h.trans_le (M.r_le_card_of_finite (hI.finite.union hJ.finite))
    rwa [add_le_iff_nonpos_left, le_zero_iff,
      ncard_eq_zero (hI.finite.subset (inter_subset_left _ _)), ← disjoint_iff_inter_eq_empty] at h'
  rw [indep_iff_r_eq_card_of_finite (hI.finite.union hJ.finite)]
  refine' (M.r_le_card_of_finite (hI.finite.union hJ.finite)).antisymm _
  linarith

theorem Skew.r_add [FiniteRk M] (h : M.Skew X Y) : M.R X + M.R Y = M.R (X ∪ Y) :=
  skew_iff_r.mp h

theorem Skew.cl_left (h : M.Skew X Y) : M.Skew (M.cl X) Y := by
  rwa [skew_iff_project_lrestr_eq_lrestr, project_cl_eq_project, ←
    skew_iff_project_lrestr_eq_lrestr]

theorem Skew.cl_left_iff : M.Skew X Y ↔ M.Skew (M.cl X) Y :=
  ⟨Skew.cl_left, fun h => h.subset_left (M.subset_cl X)⟩

theorem Skew.cl_right (h : M.Skew X Y) : M.Skew X (M.cl Y) :=
  h.symm.cl_left.symm

theorem Skew.cl_right_iff : M.Skew X Y ↔ M.Skew X (M.cl Y) :=
  ⟨Skew.cl_right, fun h => h.subset_right (M.subset_cl Y)⟩

theorem Nonloop.singleton_skew_iff (he : M.Nonloop e) : M.Skew {e} X ↔ e ∉ M.cl X :=
  by
  rw [skew.cl_right_iff]
  refine' ⟨fun h hecl => he (h.loop_of_mem_inter ⟨mem_singleton e, hecl⟩), fun h => _⟩
  obtain ⟨J, hJ⟩ := M.exists_basis X
  rw [← skew.cl_right_iff]
  have heJ : e ∉ J := not_mem_subset (hJ.subset.trans (subset_cl _ _)) h
  refine' he.indep.basis_self.skew hJ (disjoint_singleton_left.mpr heJ) _
  rwa [singleton_union, hJ.indep.insert_indep_iff_of_not_mem heJ, hJ.cl]

theorem Nonloop.skew_singleton_iff (he : M.Nonloop e) : M.Skew X {e} ↔ e ∉ M.cl X := by
  rw [skew.comm, he.singleton_skew_iff]

/-- Useful for adding a disjointness assumption when proving skewness -/
theorem skew_iff_diff_loops_skew_left : M.Skew X Y ↔ M.Skew (X \ M.cl ∅) Y := by
  rw [Iff.comm, skew.cl_left_iff, cl_diff_loops_eq_cl, ← skew.cl_left_iff]

theorem skew_iff_diff_loops_skew_right : M.Skew X Y ↔ M.Skew X (Y \ M.cl ∅) := by
  rw [Iff.comm, skew.cl_right_iff, cl_diff_loops_eq_cl, ← skew.cl_right_iff]

theorem project_skew_of_union_skew (h : M.Skew (C ∪ X) Y) : (M ⟋ C).Skew X Y :=
  by
  rw [skew, project_project, skew_iff_project_lrestr_eq_lrestr.mp h, eq_comm, ← skew]
  exact h.subset_left (subset_union_left _ _)

section Skew

variable {ι : Type _} {Xs : ι → Set E}

/-- A collection of sets is `Skew` if each of its partitions gives a skew pair  -/
def SkewCat (M : Matroid E) (Xs : ι → Set E) :=
  ∀ I : Set ι, M.Skew (⋃ i ∈ I, Xs i) (⋃ i ∈ Iᶜ, Xs i)

-- lemma Skew_iff_forall : M.Skew Xs ↔ ∀ i, M.skew (Xs i) (⋃ j ∈ ({i} : set ι)ᶜ, Xs j)  :=
-- begin
--   refine ⟨λ h i, by { convert h {i}, simp, }, λ h I, _⟩,
--   rw skew_iff_project_lrestr_eq_lrestr,
-- end
end Skew

section Separation

/-- A set is a `separator` in `M` if it is skew to its complement -/
def IsSeparator (M : Matroid E) (X : Set E) :=
  M.Skew X (Xᶜ)

end Separation

end Matroid

