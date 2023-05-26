import Matroid.Loop
import Mathlib.Tactic.Linarith.Default

/- The rank of a set in a matroid `M` is the size of one of its bases. When `M` is infinite,
  this quantity is not defined in general, so rank is not very useful when building API for
  general matroids, even though it is often the easiest way to do things for finite matroids.

  A good number of rank lemmas have both `r_fin` versions, for sets of finite rank in a matroid
  of potentially infinite rank, and `[finite_rk M]` version, which apply in the more commonly
  considered case where the entire matroid has finite rank, and are implied by the `r_fin` version.
   -/
/- The rank of a set in a matroid `M` is the size of one of its bases. When `M` is infinite,
  this quantity is not defined in general, so rank is not very useful when building API for
  general matroids, even though it is often the easiest way to do things for finite matroids.

  A good number of rank lemmas have both `r_fin` versions, for sets of finite rank in a matroid
  of potentially infinite rank, and `[finite_rk M]` version, which apply in the more commonly
  considered case where the entire matroid has finite rank, and are implied by the `r_fin` version.
   -/
noncomputable section

open Classical

open Set

namespace Matroid

variable {E : Type _} {M : Matroid E} {B X Y X' Y' Z I J : Set E} {e f x y z : E} {k n : ℕ}

section Basic

/-- The rank `r X` of a set `X` is the cardinality of one of its bases, or zero if its bases are
  infinite -/
def r {E : Type _} (M : Matroid E) (X : Set E) : ℕ :=
  ⨅ I : { I | M.Basis I X }, ncard (I : Set E)

/-- The rank `M.rk` of a matroid is the rank of its ground set -/
def rk {E : Type _} (M : Matroid E) : ℕ :=
  M.R univ

theorem rk_def {E : Type _} (M : Matroid E) : M.rk = M.R univ :=
  rfl

/-- The rank of a set is the size of a basis -/
theorem Basis.card (hI : M.Basis I X) : I.ncard = M.R X :=
  by
  have hrw : ∀ J : { J : Set E | M.basis J X }, (J : Set E).ncard = I.ncard :=
    by
    rintro ⟨J, hJ : M.basis J X⟩
    rw [Subtype.coe_mk, hI.card_eq_card_of_basis hJ]
  have : Nonempty { J : Set E | M.basis J X } :=
    let ⟨I, hI⟩ := M.exists_basis X
    ⟨⟨I, hI⟩⟩
  simp_rw [r, hrw, ciInf_const]

theorem eq_r_iff {n : ℕ} : M.R X = n ↔ ∃ I, M.Basis I X ∧ I.ncard = n :=
  by
  constructor
  · rintro rfl
    obtain ⟨I, hI⟩ := M.exists_basis X
    exact ⟨I, hI, hI.card⟩
  rintro ⟨I, hI, rfl⟩; rw [hI.card]

theorem Indep.r (hI : M.indep I) : M.R I = I.ncard :=
  eq_r_iff.mpr ⟨I, hI.basis_self, rfl⟩

theorem Basis.r (hIX : M.Basis I X) : M.R I = M.R X := by rw [← hIX.card, hIX.indep.r]

theorem Basis.r_eq_card (hIX : M.Basis I X) : M.R X = I.ncard := by rw [← hIX.r, ← hIX.indep.r]

theorem Base.r (hB : M.base B) : M.R B = M.rk :=
  by
  rw [base_iff_basis_univ] at hB
  rw [hB.r]
  rfl

theorem Base.card (hB : M.base B) : B.ncard = M.rk :=
  by
  rw [(base_iff_basis_univ.mp hB).card]
  rfl

@[simp]
theorem r_empty (M : Matroid E) : M.R ∅ = 0 := by rw [← M.empty_indep.basis_self.card, ncard_empty]

@[simp]
theorem r_cl (M : Matroid E) (X : Set E) : M.R (M.cl X) = M.R X :=
  by
  let ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.r, ← hI.cl, hI.indep.basis_cl.r]

@[simp]
theorem r_union_cl_right_eq_r_union (M : Matroid E) (X Y : Set E) :
    M.R (X ∪ M.cl Y) = M.R (X ∪ Y) := by rw [← r_cl, cl_union_cl_right_eq_cl_union, r_cl]

@[simp]
theorem r_union_cl_left_eq_r_union (M : Matroid E) (X Y : Set E) : M.R (M.cl X ∪ Y) = M.R (X ∪ Y) :=
  by rw [← r_cl, cl_union_cl_left_eq_cl_union, r_cl]

@[simp]
theorem r_insert_cl_eq_r_insert (M : Matroid E) (e : E) (X : Set E) :
    M.R (insert e (M.cl X)) = M.R (insert e X) := by
  rw [← union_singleton, r_union_cl_left_eq_r_union, union_singleton]

theorem Basis.r_eq_r_union (hIX : M.Basis I X) (Y : Set E) : M.R (I ∪ Y) = M.R (X ∪ Y) :=
  by
  obtain ⟨I', hI', hII'⟩ :=
    hIX.indep.subset_basis_of_subset (hIX.subset.trans (subset_union_left _ Y))
  rw [← hI'.r, ← (hI'.basis_subset _ (union_subset_union_left Y hIX.subset)).R]
  refine' fun e he =>
    (hI'.subset he).elim (fun heX => Or.inl _) fun heY => subset_union_right _ _ heY
  exact hIX.mem_of_insert_indep heX (hI'.indep.subset (insert_subset.mpr ⟨he, hII'⟩))

section Finite

theorem r_le_card_of_finite (M : Matroid E) {X : Set E} (h : X.Finite) : M.R X ≤ X.ncard :=
  let ⟨I, hI⟩ := M.exists_basis X
  hI.card.symm.le.trans (ncard_le_of_subset hI.Subset h)

theorem r_le_card [Finite E] (M : Matroid E) (X : Set E) : M.R X ≤ X.ncard :=
  M.r_le_card_of_finite (toFinite X)

theorem indep_iff_r_eq_card_of_finite {M : Matroid E} (hI : I.Finite) :
    M.indep I ↔ M.R I = I.ncard :=
  by
  obtain ⟨J, hJ⟩ := M.exists_basis I
  rw [← hJ.card]
  refine' ⟨fun h => by rw [h.eq_of_basis hJ], fun h => _⟩
  rw [← eq_of_subset_of_ncard_le hJ.subset h.symm.le hI]
  exact hJ.indep

theorem indep_iff_r_eq_card [Finite E] : M.indep I ↔ M.R I = I.ncard :=
  indep_iff_r_eq_card_of_finite (toFinite _)

theorem rk_le_card [Finite E] (M : Matroid E) : M.rk ≤ Nat.card E :=
  (M.r_le_card univ).trans (ncard_univ _).le

theorem r_lt_card_of_dep_of_finite (h : X.Finite) (hX : ¬M.indep X) : M.R X < X.ncard :=
  lt_of_le_of_ne (M.r_le_card_of_finite h) (by rwa [indep_iff_r_eq_card_of_finite h] at hX)

theorem r_lt_card_of_dep [Finite E] (hX : ¬M.indep X) : M.R X < X.ncard :=
  r_lt_card_of_dep_of_finite (toFinite _) hX

theorem r_lt_card_iff_dep_of_finite (hX : X.Finite) : M.R X < X.ncard ↔ ¬M.indep X :=
  ⟨fun h hI => h.Ne hI.R, r_lt_card_of_dep_of_finite hX⟩

theorem r_lt_card_iff_dep [Finite E] : M.R X < X.ncard ↔ ¬M.indep X :=
  ⟨fun h hI => h.Ne hI.R, r_lt_card_of_dep⟩

end Finite

section RFin

/-- `M.r_fin X` means that `X` has a finite basis in `M`-/
def RFin (M : Matroid E) (X : Set E) : Prop :=
  ∃ I, M.Basis I X ∧ I.Finite

theorem RFin.exists_finite_basis (h : M.RFin X) : ∃ I, M.Basis I X ∧ I.Finite :=
  h

theorem Basis.finite_of_rFin (h : M.Basis I X) (hX : M.RFin X) : I.Finite :=
  by
  obtain ⟨J, hJ, hJfin⟩ := hX
  exact hJ.finite_of_finite hJfin h

theorem Basis.rFin_of_finite (hIX : M.Basis I X) (h : I.Finite) : M.RFin X :=
  ⟨I, hIX, h⟩

theorem Basis.rFin_iff_finite (hIX : M.Basis I X) : M.RFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

theorem Indep.rFin_iff_finite (hI : M.indep I) : M.RFin I ↔ I.Finite :=
  hI.basis_self.rFin_iff_finite

theorem Indep.finite_of_rFin (hI : M.indep I) (hfin : M.RFin I) : I.Finite :=
  hI.basis_self.finite_of_rFin hfin

theorem Indep.subset_finite_basis_of_subset_of_rFin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.RFin X) :
    ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun J hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rFin hX⟩

theorem to_rFin (M : Matroid E) [FiniteRk M] (X : Set E) : M.RFin X :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  exact ⟨I, hI, hI.finite⟩

theorem rFin_of_finite (M : Matroid E) (hX : X.Finite) : M.RFin X :=
  Exists.elim (M.exists_basis X) fun I hI => hI.rFin_of_finite (hX.Subset hI.Subset)

theorem rFin_singleton (M : Matroid E) (e : E) : M.RFin {e} :=
  M.rFin_of_finite (finite_singleton e)

@[simp]
theorem rFin_empty (M : Matroid E) : M.RFin ∅ :=
  M.rFin_of_finite finite_empty

theorem RFin.subset (h : M.RFin Y) (hXY : X ⊆ Y) : M.RFin X :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  exact hI.r_fin_of_finite ((hJ.finite_of_r_fin h).Subset hIJ)

theorem RFin.finite_of_indep_subset (hX : M.RFin X) (hI : M.indep I) (hIX : I ⊆ X) : I.Finite :=
  Exists.elim (hI.subset_finite_basis_of_subset_of_rFin hIX hX) fun J hJ => hJ.2.2.Subset hJ.2.1

theorem Indep.finite_of_subset_rFin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.RFin X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

theorem RFin.to_cl (h : M.RFin X) : M.RFin (M.cl X) :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rwa [← hI.cl, hI.indep.basis_cl.r_fin_iff_finite, ← hI.r_fin_iff_finite]

@[simp]
theorem rFin_cl_iff : M.RFin (M.cl X) ↔ M.RFin X :=
  ⟨fun h => h.Subset (M.subset_cl _), RFin.to_cl⟩

/-- A set with no finite basis has the junk rank value of zero -/
theorem r_eq_zero_of_not_rFin (h : ¬M.RFin X) : M.R X = 0 :=
  by
  simp_rw [r_fin, not_exists, not_and] at h
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.card, infinite.ncard (h _ hI)]

theorem rFin_of_r_ne_zero (h : M.R X ≠ 0) : M.RFin X :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.card] at h
  exact hI.r_fin_of_finite (finite_of_ncard_ne_zero h)

theorem RFin.union (hX : M.RFin X) (hY : M.RFin Y) : M.RFin (X ∪ Y) :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [← r_fin_cl_iff, ← cl_union_cl_left_eq_cl_union, ← hI.cl, cl_union_cl_left_eq_cl_union, ←
    cl_union_cl_right_eq_cl_union, ← hJ.cl, cl_union_cl_right_eq_cl_union, r_fin_cl_iff]
  exact M.r_fin_of_finite ((hI.finite_of_r_fin hX).union (hJ.finite_of_r_fin hY))

theorem RFin.insert (hX : M.RFin X) (e : E) : M.RFin (insert e X) :=
  (M.rFin_singleton e).union hX

theorem Indep.le_card_basis_of_rFin (hI : M.indep I) (hIX : I ⊆ X) (hX : M.RFin X)
    (hXJ : M.Basis J X) : I.ncard ≤ J.ncard :=
  by
  obtain ⟨I', hI, h⟩ := hI.subset_finite_basis_of_subset_of_r_fin hIX hX
  rw [hXJ.card_eq_card_of_basis hI]
  exact ncard_le_of_subset h.1 (hI.finite_of_r_fin hX)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem RFin.le_r_iff (h : M.RFin X) {n : ℕ} :
    n ≤ M.R X ↔ ∃ (I : _)(_ : I ⊆ X), M.indep I ∧ I.ncard = n :=
  by
  obtain ⟨J, hJ⟩ := eq_r_iff.mp (@rfl _ (M.r X))
  refine' ⟨fun h => _, fun h => _⟩
  · obtain ⟨I', hI', rfl⟩ := exists_smaller_set _ _ (h.trans_eq hJ.2.symm)
    exact ⟨I', hI'.trans hJ.1.Subset, hJ.1.indep.Subset hI', by simp⟩
  obtain ⟨I, hIX, hI, rfl⟩ := h
  rw [← hJ.2]
  exact hI.le_card_basis_of_r_fin hIX h hJ.1

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem RFin.r_le_iff (h : M.RFin X) {n : ℕ} :
    M.R X ≤ n ↔ ∀ (I) (_ : I ⊆ X), M.indep I → I.ncard ≤ n :=
  by
  obtain ⟨I, hIX, hI⟩ := eq_r_iff.mp (@rfl _ (M.r X))
  exact
    ⟨fun h' J hJX hJ => (hJ.le_card_basis_of_rFin hJX h hIX).trans (hI.trans_le h'), fun h =>
      hI.symm.trans_le (h I hIX.subset hIX.indep)⟩

theorem RFin.r_mono (hY : M.RFin Y) (hXY : X ⊆ Y) : M.R X ≤ M.R Y :=
  by
  simp_rw [(hY.subset hXY).r_le_iff, hY.le_r_iff]
  exact fun I hIX hI => ⟨I, hIX.trans hXY, hI, rfl⟩

theorem RFin.r_eq_r_of_subset_le (h : M.RFin Y) (hXY : X ⊆ Y) (hYX : M.R Y ≤ M.R X) :
    M.R X = M.R Y :=
  (h.r_mono hXY).antisymm hYX

theorem Indep.card_le_r_of_subset_of_rFin (hI : M.indep I) (h : I ⊆ X) (hX : M.RFin X) :
    I.ncard ≤ M.R X := by
  rw [← hI.r]
  exact hX.r_mono h

theorem Indep.basis_of_subset_of_r_le_of_rFin (hI : M.indep I) (hIX : I ⊆ X) (h : M.R X ≤ M.R I)
    (hX : M.RFin X) : M.Basis I X :=
  by
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIX
  rwa [eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_r_fin hX)]
  rwa [hJ.card, ← hI.r]

/-- The submodularity axiom for the rank function -/
theorem RFin.r_inter_add_r_union_le_r_add_r (hX : M.RFin X) (hY : M.RFin Y) :
    M.R (X ∩ Y) + M.R (X ∪ Y) ≤ M.R X + M.R Y :=
  by
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y)
  obtain ⟨IX, hIX, hIX', hIXfin⟩ :=
    hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_left _ _)) hX
  obtain ⟨IY, hIY, hIY', hIYfin⟩ :=
    hIi.indep.subset_finite_basis_of_subset_of_r_fin (hIi.subset.trans (inter_subset_right _ _)) hY
  rw [← hIX.r_eq_r_union, union_comm, ← hIY.r_eq_r_union, ← hIi.card, ← hIX.card, ← hIY.card,
    union_comm, ← ncard_union_add_ncard_inter _ _ hIXfin hIYfin, add_comm]
  refine' add_le_add (M.r_le_card_of_finite (hIXfin.union hIYfin)) _
  refine' ncard_le_of_subset (subset_inter hIX' hIY') (hIXfin.subset (inter_subset_left _ _))

alias r_fin.r_inter_add_r_union_le_r_add_r ← r_fin.submod

theorem RFin.r_union_le_add_r (hX : M.RFin X) (hY : M.RFin Y) : M.R (X ∪ Y) ≤ M.R X + M.R Y := by
  linarith [hX.submod hY]

theorem RFin.basis_iff_finite_indep_card (hX : M.RFin X) :
    M.Basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.Finite ∧ I.ncard = M.R X :=
  by
  refine'
    I.finite_or_infinite.symm.elim _ fun hI =>
      ⟨fun hb => ⟨hb.indep, hb.Subset, hI, hb.card⟩, fun h => _⟩
  ·
    exact fun hI =>
      iff_of_false (fun hb => hI (hb.finite_of_rFin hX)) (by simp [iff_false_intro hI])
  refine' h.1.basis_of_maximal_subset h.2.1 fun J hJ hIJ hJX => _
  rw [← eq_of_subset_of_ncard_le hIJ _ (hJ.finite_of_subset_r_fin hJX hX)]
  rw [h.2.2.2, hX.le_r_iff]
  exact ⟨J, hJX, hJ, rfl⟩

theorem Indep.basis_of_rFin_of_subset_of_r_ge (hI : M.indep I) (hIX : I ⊆ X) (hX : M.RFin X)
    (hr : M.R X ≤ I.ncard) : M.Basis I X :=
  hX.basis_iff_finite_indep_card.mpr
    ⟨hI, hIX, hI.finite_of_subset_rFin hIX hX, hr.antisymm' (hX.le_r_iff.mpr ⟨I, hIX, hI, rfl⟩)⟩

theorem RFin.r_eq_zero_iff_subset_loops (hX : M.RFin X) : M.R X = 0 ↔ X ⊆ M.cl ∅ :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← cl_subset_cl_iff_subset_cl, ← hI.cl]
  rw [hX.basis_iff_finite_indep_card] at hI
  rw [← hI.2.2.2, ncard_eq_zero hI.2.2.1]
  exact
    ⟨by
      rintro rfl
      exact subset.rfl, fun h => hI.1.eq_empty_of_subset_loops ((M.subset_cl I).trans h)⟩

theorem RFin.r_eq_r_diff_r_le_zero (hY : M.RFin Y) (X) (hr : M.R Y ≤ 0) : M.R (X \ Y) = M.R X := by
  rw [← r_cl, cl_diff_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)),
    r_cl]

theorem RFin.r_eq_r_union_r_le_zero (hY : M.RFin Y) (X) (hr : M.R Y ≤ 0) : M.R (X ∪ Y) = M.R X := by
  rw [← r_cl, cl_union_eq_cl_of_subset_loops (hY.r_eq_zero_iff_subset_loops.mp (le_zero_iff.mp hr)),
    r_cl]

theorem RFin.r_le_r_inter_add_r_diff (hX : M.RFin X) (Y : Set E) :
    M.R X ≤ M.R (X ∩ Y) + M.R (X \ Y) :=
  by
  convert r_fin.r_union_le_add_r (hX.subset (inter_subset_left _ _)) (hX.subset (diff_subset _ _))
  rw [inter_union_diff X Y]

theorem RFin.r_le_r_add_r_diff (hX : M.RFin X) (hYX : Y ⊆ X) : M.R X ≤ M.R Y + M.R (X \ Y) :=
  by
  convert hX.r_le_r_inter_add_r_diff _
  rw [inter_eq_self_of_subset_right hYX]

theorem RFin.cl_eq_cl_of_subset_of_r_ge_r (hY : M.RFin Y) (hXY : X ⊆ Y) (hr : M.R Y ≤ M.R X) :
    M.cl X = M.cl Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ, hIJ, hJfin⟩ :=
    hI.indep.subset_finite_basis_of_subset_of_r_fin (hI.subset.trans hXY) hY
  rw [← hI.cl, ← hJ.cl, eq_of_subset_of_ncard_le hIJ _ hJfin]
  rwa [hI.card, hJ.card]

end RFin

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem le_r_iff [FiniteRk M] : n ≤ M.R X ↔ ∃ (I : _)(_ : I ⊆ X), M.indep I ∧ I.ncard = n :=
  (M.to_rFin X).le_r_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem r_le_iff [FiniteRk M] : M.R X ≤ n ↔ ∀ (I) (_ : I ⊆ X), M.indep I → I.ncard ≤ n :=
  (M.to_rFin X).r_le_iff

theorem r_mono (M : Matroid E) [FiniteRk M] {X Y : Set E} (hXY : X ⊆ Y) : M.R X ≤ M.R Y :=
  (M.to_rFin _).r_mono hXY

theorem basis_iff_indep_card [FiniteRk M] : M.Basis I X ↔ M.indep I ∧ I ⊆ X ∧ I.ncard = M.R X :=
  by
  rw [(M.to_r_fin X).basis_iff_finite_indep_card]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun h => ⟨h.1, h.2.1, h.1.Finite, h.2.2⟩⟩

theorem r_le_rk (M : Matroid E) [FiniteRk M] (X : Set E) : M.R X ≤ M.rk :=
  M.r_mono (subset_univ _)

theorem lt_rk_iff_ne_rk [FiniteRk M] : M.R X < M.rk ↔ M.R X ≠ M.rk :=
  (M.r_le_rk X).lt_iff_ne

theorem Indep.card_le_r_of_subset [FiniteRk M] (hI : M.indep I) (h : I ⊆ X) : I.ncard ≤ M.R X :=
  by
  rw [← hI.r]
  exact M.r_mono h

theorem Indep.card_le_rk [FiniteRk M] (hI : M.indep I) : I.ncard ≤ M.rk :=
  hI.R.symm.trans_le (M.r_mono (subset_univ I))

theorem base_iff_indep_r [FiniteRk M] : M.base B ↔ M.indep B ∧ M.R B = M.rk :=
  by
  refine' ⟨fun h => ⟨h.indep, h.R⟩, fun h => base_iff_maximal_indep.mpr ⟨h.1, fun I hI hBI => _⟩⟩
  refine' eq_of_le_of_not_lt hBI fun hBI' : B ⊂ I => _
  cases' h with hB hB'
  rw [hB.r] at hB'
  have := ncard_lt_ncard hBI' hI.finite
  rw [← hI.r, hB'] at this
  exact (M.r_mono (subset_univ _)).not_lt this

theorem base_iff_indep_card [FiniteRk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
  ⟨fun h => ⟨h.indep, by rw [← h.card]⟩, fun h =>
    base_iff_indep_r.mpr ⟨h.1, by rw [← h.2, ← h.1.R]⟩⟩

theorem Indep.base_of_rk_le_card [FiniteRk M] (hI : M.indep I) (h : M.rk ≤ I.ncard) : M.base I :=
  base_iff_indep_card.mpr
    ⟨hI,
      h.antisymm'
        (by
          rw [← hI.r]
          apply r_le_rk)⟩

theorem Basis.r_eq_r_insert (hIX : M.Basis I X) (e : E) : M.R (insert e I) = M.R (insert e X) := by
  simp_rw [← union_singleton, hIX.r_eq_r_union]

theorem Indep.basis_of_subset_of_r_le [FiniteRk M] (hI : M.indep I) (hIX : I ⊆ X)
    (h : M.R X ≤ M.R I) : M.Basis I X :=
  hI.basis_of_subset_of_r_le_of_rFin hIX h (M.to_rFin X)

/-- The submodularity axiom for the rank function -/
theorem r_inter_add_r_union_le_r_add_r (M : Matroid E) [FiniteRk M] (X Y : Set E) :
    M.R (X ∩ Y) + M.R (X ∪ Y) ≤ M.R X + M.R Y :=
  (M.to_rFin X).r_inter_add_r_union_le_r_add_r (M.to_rFin Y)

alias r_inter_add_r_union_le_r_add_r ← r_submod

theorem eq_of_r_eq_r_forall {M₁ M₂ : Matroid E} [FiniteRk M₁] (h : ∀ X, M₁.R X = M₂.R X) :
    M₁ = M₂ :=
  by
  have h2 : ∀ I, M₂.indep I → I.Finite :=
    by
    refine' fun I hI => by_contra fun hinf : I.Infinite => _
    obtain ⟨B₁, hB₁⟩ := M₁.exists_base
    obtain ⟨I₁, hI₁I, hI₁fin, hI₁card⟩ := hinf.exists_subset_ncard_eq (M₁.rk + 1)
    rw [← (hI.subset hI₁I).R, ← h] at hI₁card
    linarith [M₁.r_le_rk I₁]
  refine'
    eq_of_indep_iff_indep_forall fun I =>
      I.finite_or_infinite.symm.elim
        (fun hI => iff_of_false (fun h' => hI h'.Finite) fun h' => hI (h2 _ h')) fun hI => _
  rw [indep_iff_r_eq_card_of_finite hI, h, indep_iff_r_eq_card_of_finite hI]

theorem r_le_r_of_subset (M : Matroid E) [FiniteRk M] (hXY : X ⊆ Y) : M.R X ≤ M.R Y :=
  M.r_mono hXY

theorem r_inter_left_le_r (M : Matroid E) [FiniteRk M] (X Y : Set E) : M.R (X ∩ Y) ≤ M.R X :=
  M.r_mono (inter_subset_left X Y)

theorem r_inter_right_le_r (M : Matroid E) [FiniteRk M] (X Y : Set E) : M.R (X ∩ Y) ≤ M.R Y :=
  M.r_mono (inter_subset_right X Y)

theorem r_le_r_union_left (M : Matroid E) [FiniteRk M] (X Y : Set E) : M.R X ≤ M.R (X ∪ Y) :=
  M.r_mono (subset_union_left X Y)

theorem r_le_r_union_right (M : Matroid E) [FiniteRk M] (X Y : Set E) : M.R Y ≤ M.R (X ∪ Y) :=
  M.r_mono (subset_union_right X Y)

theorem r_diff_le_r (M : Matroid E) [FiniteRk M] (X Y : Set E) : M.R (X \ Y) ≤ M.R X :=
  by
  rw [diff_eq]
  apply r_inter_left_le_r

theorem r_lt_card_iff_not_indep [Finite E] : M.R X < X.ncard ↔ ¬M.indep X :=
  by
  rw [lt_iff_not_le, not_iff_not, indep_iff_r_eq_card]
  exact ⟨(M.r_le_card X).antisymm, fun h => by rw [h]⟩

theorem nonempty_of_r_nonzero (hX : M.R X ≠ 0) : X.Nonempty :=
  by
  rw [nonempty_iff_ne_empty]
  rintro rfl
  exact hX M.r_empty

theorem r_single_ub (M : Matroid E) [FiniteRk M] (e : E) : M.R {e} ≤ 1 := by
  convert M.r_le_card_of_finite _ <;> simp [ncard_singleton]

theorem r_eq_r_of_subset_le [FiniteRk M] (hXY : X ⊆ Y) (hYX : M.R Y ≤ M.R X) : M.R X = M.R Y :=
  (M.r_mono hXY).antisymm hYX

theorem r_eq_r_diff_r_le_zero [FiniteRk M] (X : Set E) (hY : M.R Y ≤ 0) : M.R (X \ Y) = M.R X :=
  (M.to_rFin Y).r_eq_r_diff_r_le_zero _ hY

theorem r_eq_r_union_r_le_zero [FiniteRk M] (X : Set E) (hY : M.R Y ≤ 0) : M.R (X ∪ Y) = M.R X :=
  (M.to_rFin Y).r_eq_r_union_r_le_zero _ hY

theorem cl_eq_cl_of_subset_of_r_ge_r [FiniteRk M] (hXY : X ⊆ Y) (hr : M.R Y ≤ M.R X) :
    M.cl X = M.cl Y :=
  (M.to_rFin Y).cl_eq_cl_of_subset_of_r_ge_r hXY hr

theorem r_union_eq_of_subset_of_r_le_r [FiniteRk M] (Z : Set E) (hXY : X ⊆ Y) (hr : M.R Y ≤ M.R X) :
    M.R (X ∪ Z) = M.R (Y ∪ Z) := by
  rw [← r_cl, ← cl_union_cl_left_eq_cl_union, cl_eq_cl_of_subset_of_r_ge_r hXY hr,
    cl_union_cl_left_eq_cl_union, r_cl]

-- lemma r_union_eq_of_subset_of_r_eqs (hX : X ⊆ X') (hY : Y ⊆ Y')
-- (hXX' : M.r X = M.r X') (hYY' : M.r Y = M.r Y') :
--   M.r (X ∪ Y) = M.r (X' ∪ Y') :=
-- by rw [r_union_eq_of_subset_of_r_eq Y hX hXX', union_comm, union_comm _ Y',
--        r_union_eq_of_subset_of_r_eq _ hY hYY']
-- lemma r_eq_of_inter_union (X Y A : set E) :
--   M.r (X ∩ A) = M.r X → M.r ((X ∩ A) ∪ Y) = M.r (X ∪ Y) :=
-- λ h, r_union_eq_of_subset_of_r_eq _ (inter_subset_left _ _) h
-- lemma r_eq_of_union_r_diff_eq (Z : set E) (hX : M.r (X \ Y) = M.r X) :
--   M.r (Z ∪ (X \ Y)) = M.r (Z ∪ X) :=
-- by {rw diff_eq at *, rw [union_comm _ X, ← r_eq_of_inter_union _ Z _ hX, union_comm Z]}
theorem r_union_le_add_r (M : Matroid E) [FiniteRk M] (X Y : Set E) : M.R (X ∪ Y) ≤ M.R X + M.R Y :=
  by linarith [M.r_submod X Y]

theorem r_union_le_card_add_r [Finite E] (M : Matroid E) (X Y : Set E) :
    M.R (X ∪ Y) ≤ X.ncard + M.R Y :=
  (M.r_union_le_add_r X Y).trans (add_le_add_right (M.r_le_card _) _)

theorem r_union_le_r_add_card [Finite E] (M : Matroid E) (X Y : Set E) :
    M.R (X ∪ Y) ≤ M.R X + Y.ncard :=
  (M.r_union_le_add_r X Y).trans (add_le_add_left (M.r_le_card _) _)

theorem rk_le_card_add_r_compl [Finite E] (M : Matroid E) (X : Set E) : M.rk ≤ X.ncard + M.R (Xᶜ) :=
  by
  rw [rk, ← union_compl_self X]
  exact (M.r_union_le_add_r _ _).trans (add_le_add_right (M.r_le_card _) _)

theorem rank_eq_of_le_supset [FiniteRk M] (h : X ⊆ Y) (hr : M.R Y ≤ M.R X) : M.R X = M.R Y :=
  hr.antisymm' (M.r_mono h)

theorem r_le_r_insert (M : Matroid E) (e : E) (X : Set E) : M.R X ≤ M.R (insert e X) :=
  (em (M.RFin X)).symm.elim (fun hX => by simp [r_eq_zero_of_not_r_fin hX]) fun hX =>
    (hX.insert e).r_mono (subset_insert _ _)

theorem r_insert_le_add_one (M : Matroid E) (e : E) (X : Set E) : M.R (insert e X) ≤ M.R X + 1 :=
  by
  refine' (em (M.r_fin X)).symm.elim (fun hX => _) fun hX => _
  · convert Nat.zero_le _
    rw [r_eq_zero_of_not_r_fin]
    exact fun h => hX (h.Subset (subset_insert _ _))
  refine' ((M.r_fin_singleton e).r_union_le_add_r hX).trans _
  rw [add_comm, add_le_add_iff_left, ← ncard_singleton e]
  exact M.r_le_card_of_finite (finite_singleton e)

theorem r_eq_of_le_insert (h : M.R (insert e X) ≤ M.R X) : M.R (insert e X) = M.R X :=
  h.antisymm (M.r_le_r_insert e X)

theorem r_insert_eq_add_one_of_r_ne (h : M.R (insert e X) ≠ M.R X) : M.R (insert e X) = M.R X + 1 :=
  (Nat.lt_iff_add_one_le.mp ((M.r_le_r_insert e X).lt_of_ne h.symm)).antisymm'
    (M.r_insert_le_add_one e X)

theorem r_insert_eq_add_one_iff_r_ne : M.R (insert e X) = M.R X + 1 ↔ M.R (insert e X) ≠ M.R X :=
  ⟨by
    intro h
    rw [h]
    exact (r M X).succ_ne_self, r_insert_eq_add_one_of_r_ne⟩

theorem r_le_r_add_r_diff (M : Matroid E) [FiniteRk M] (X Y : Set E) :
    M.R Y ≤ M.R X + M.R (Y \ X) :=
  le_trans (M.r_mono (by simp)) (r_union_le_add_r M X (Y \ X))

theorem r_le_r_diff_singleton_add_one (M : Matroid E) (e : E) (X : Set E) :
    M.R X ≤ M.R (X \ {e}) + 1 :=
  by
  refine' le_trans _ (M.r_insert_le_add_one e (X \ {e}))
  rw [insert_diff_singleton]
  apply r_le_r_insert

theorem r_diff_singleton_add_one_eq_r_of_ne (h_ne : M.R X ≠ M.R (X \ {e})) :
    M.R X = M.R (X \ {e}) + 1 :=
  by
  refine'
    (em (e ∈ X)).symm.elim (fun h => (h_ne (by rw [diff_singleton_eq_self h])).elim) fun he => _
  convert@r_insert_eq_add_one_of_r_ne _ _ _ e _ <;> rwa [insert_diff_singleton, insert_eq_of_mem he]

theorem r_le_r_add_card_diff_of_subset [Finite E] (M : Matroid E) (hXY : X ⊆ Y) :
    M.R Y ≤ M.R X + (Y \ X).ncard :=
  (M.r_le_r_add_r_diff X Y).trans (add_le_add_left (by convert M.r_le_card (Y \ X)) _)

theorem r_add_card_le_r_add_card_of_subset [Finite E] (M : Matroid E) (hXY : X ⊆ Y) :
    M.R Y + X.ncard ≤ M.R X + Y.ncard :=
  by
  have := M.r_le_r_add_card_diff_of_subset hXY
  linarith [ncard_diff_add_ncard_eq_ncard hXY]

theorem submod_three (M : Matroid E) [FiniteRk M] (X Y Y' : Set E) :
    M.R (X ∪ (Y ∪ Y')) + M.R (X ∪ Y ∩ Y') ≤ M.R (X ∪ Y) + M.R (X ∪ Y') :=
  by
  have := M.r_submod (X ∪ Y) (X ∪ Y')
  rwa [← union_distrib_left, ← union_union_distrib_left, add_comm] at this

theorem submod_three_right (M : Matroid E) [FiniteRk M] (X Y Y' : Set E) :
    M.R (Y ∪ Y' ∪ X) + M.R (Y ∩ Y' ∪ X) ≤ M.R (Y ∪ X) + M.R (Y' ∪ X) :=
  by
  simp_rw [← union_comm X]
  apply submod_three

theorem submod_three_disj (M : Matroid E) [FiniteRk M] (X Y Y' : Set E) (hYY' : Y ∩ Y' = ∅) :
    M.R (X ∪ (Y ∪ Y')) + M.R X ≤ M.R (X ∪ Y) + M.R (X ∪ Y') :=
  by
  have := submod_three M X Y Y'
  rwa [hYY', union_empty] at this

theorem r_union_add_r_le_r_union_add_r_of_subset (M : Matroid E) [FiniteRk M] (hXY : X ⊆ Y)
    (Z : Set E) : M.R (Y ∪ Z) + M.R X ≤ M.R (X ∪ Z) + M.R Y :=
  by
  have hsm := M.r_submod (X ∪ Z) Y
  rw [union_right_comm, union_eq_right_iff_subset.mpr hXY, inter_distrib_right,
    inter_eq_left_iff_subset.mpr hXY, add_comm] at hsm
  exact le_trans (add_le_add_left (M.r_le_r_union_left _ _) _) hsm

theorem RFin.r_augment (hX : M.RFin X) (hZ : M.RFin Z) (h : M.R X < M.R Z) :
    ∃ z ∈ Z \ X, M.R (insert z X) = M.R X + 1 :=
  by
  obtain ⟨I, hI, hIfin⟩ := hX.exists_finite_basis
  obtain ⟨J, hJ⟩ := M.exists_basis Z
  refine' (hI.indep.augment_of_finite hJ.indep hIfin (by rwa [hI.card, hJ.card])).imp fun e => _
  rintro ⟨he, heI, hi⟩
  refine' ⟨⟨hJ.subset he, fun heX => heI (hI.mem_of_insert_indep heX hi)⟩, _⟩
  rw [← hI.r, hI.indep.r, ← ncard_insert_of_not_mem heI hIfin, ← hi.r, ← r_insert_cl_eq_r_insert, ←
    hI.cl, r_insert_cl_eq_r_insert]

theorem RFin.augment_of_not_rFin (hX : M.RFin X) (hZ : ¬M.RFin Z) :
    ∃ z ∈ Z \ X, M.R (insert z X) = M.R X + 1 :=
  by
  obtain ⟨J, hJ⟩ := M.exists_basis Z
  have hJinf : J.infinite := by rwa [Set.Infinite, ← hJ.r_fin_iff_finite]
  obtain ⟨J', hJ'J, hJfin, hJcard⟩ := hJinf.exists_subset_ncard_eq (M.r X + 1)
  obtain ⟨z, ⟨hzJ', hzX⟩, h⟩ :=
    hX.r_augment (M.r_fin_of_finite hJfin)
      (((lt_add_one _).trans_eq hJcard.symm).trans_eq (hJ.indep.subset hJ'J).R.symm)
  exact ⟨z, ⟨hJ.subset (hJ'J hzJ'), hzX⟩, h⟩

-- (M.to_r_fin X).r_augment (M.to_r_fin Z) h
theorem r_union_eq_of_r_union_subset_le [FiniteRk M] (hXY : X ⊆ Y) (h : M.R (X ∪ Z) ≤ M.R X) :
    M.R (Y ∪ Z) = M.R Y := by
  have hsm := M.r_submod Y (X ∪ Z)
  rw [← union_assoc, union_eq_left_iff_subset.mpr hXY, inter_distrib_left,
    inter_eq_right_iff_subset.mpr hXY] at hsm
  linarith [M.r_le_r_union_left X (Y ∩ Z), M.r_le_r_union_left Y Z]

theorem r_insert_eq_of_r_insert_subset_le [FiniteRk M] (hXY : X ⊆ Y)
    (h : M.R (insert e X) ≤ M.R X) : M.R (insert e Y) = M.R Y :=
  by
  rw [← union_singleton] at *
  rw [r_union_eq_of_r_union_subset_le hXY h]

theorem r_eq_of_r_all_insert_le (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.R (insert e X) ≤ M.R X) :
    M.R X = M.R Y :=
  by
  refine'
    (em (M.r_fin Y)).symm.elim (fun hYinf => _) fun hYfin =>
      (hYfin.r_mono hXY).antisymm (le_of_not_lt fun hlt => _)
  · refine' (em (M.r_fin X)).symm.elim (fun hX => _) fun hX => _
    · rw [r_eq_zero_of_not_r_fin hX, r_eq_zero_of_not_r_fin hYinf]
    obtain ⟨e, ⟨heY, -⟩, hr'⟩ := hX.augment_of_not_r_fin hYinf
    linarith [hY e heY]
  obtain ⟨e, he, hre⟩ := (hYfin.subset hXY).r_augment hYfin hlt
  linarith [hY e he.1]

theorem r_union_eq_of_r_all_insert_le (hY : ∀ e ∈ Y, M.R (insert e X) ≤ M.R X) :
    M.R (X ∪ Y) = M.R X :=
  by
  refine' (r_eq_of_r_all_insert_le (subset_union_left X Y) _).symm
  rintro e (heX | heY)
  · rw [insert_eq_of_mem heX]
  exact hY _ heY

theorem r_eq_of_r_all_insert_eq (hXY : X ⊆ Y) (hY : ∀ e ∈ Y, M.R X = M.R (insert e X)) :
    M.R X = M.R Y :=
  r_eq_of_r_all_insert_le hXY fun e h => (hY e h).symm.le

theorem indep_inter_r_zero_eq_empty [FiniteRk M] (hI : M.indep I) (hX : M.R X = 0) : I ∩ X = ∅ :=
  by
  have h := hI.subset (inter_subset_left _ X)
  rw [← ncard_eq_zero (hI.finite.subset (inter_subset_left _ _)), ← le_zero_iff]
  rw [indep_iff_r_eq_card_of_finite (hI.finite.subset (inter_subset_left _ _))] at h
  rw [← h]; exact (M.r_mono (inter_subset_right I X)).trans_eq hX

theorem base_iff_indep_card_eq_r [FiniteRk M] : M.base B ↔ M.indep B ∧ B.ncard = M.rk :=
  by
  refine'
    ⟨fun hB => ⟨hB.indep, hB.card⟩, fun h =>
      base_iff_maximal_indep.mpr ⟨h.1, fun I hI hBI => eq_of_subset_of_ncard_le hBI _ hI.Finite⟩⟩
  rw [h.2]; exact hI.card_le_rk

end Basic

section Circuit

variable {C : Set E}

theorem Circuit.finite_of_rFin (hC : M.Circuit C) (hCfin : M.RFin C) : C.Finite :=
  by
  obtain ⟨e, he⟩ := hC.nonempty
  convert((hC.diff_singleton_indep he).finite_of_rFin (hCfin.subset (diff_subset _ _))).insert e
  rw [insert_diff_singleton, insert_eq_of_mem he]

theorem Circuit.rFin_iff_finite (hC : M.Circuit C) : M.RFin C ↔ C.Finite :=
  ⟨hC.finite_of_rFin, M.rFin_of_finite⟩

theorem Circuit.card_of_finite (hC : M.Circuit C) (hfin : C.Finite) : C.ncard = M.R C + 1 :=
  by
  obtain ⟨e, he⟩ := hC.nonempty
  have hss : C \ {e} ⊂ C :=
    by
    refine' ssubset_of_ne_of_subset _ (diff_subset _ _)
    simpa only [Ne.def, sdiff_eq_left, disjoint_singleton_right, not_not_mem]
  have hlb := (M.r_fin_of_finite hfin).r_mono hss.subset
  rw [(hC.ssubset_indep hss).R] at hlb
  linarith [ncard_diff_singleton_add_one he hfin, r_lt_card_of_dep_of_finite hfin hC.dep]

theorem Circuit.card [Finitary M] (hC : M.Circuit C) : C.ncard = M.R C + 1 :=
  hC.card_of_finite hC.Finite

/-- This lemma is phrased in terms of `nat` subtraction; it never underflows but is probably still
  best avoided -/
theorem Circuit.nat_r_eq [Finitary M] (hC : M.Circuit C) : M.R C = C.ncard - 1 := by
  rw [hC.card, Nat.add_succ_sub_one, add_zero]

theorem Circuit.cast_r_eq [Finitary M] (hC : M.Circuit C) : (M.R C : ℤ) = C.ncard - 1 := by
  rw [hC.card, Nat.cast_add, Nat.cast_one, add_tsub_cancel_right]

theorem exists_circuit_iff_card_lt_rk [Finite E] : M.rk < (univ : Set E).ncard ↔ ∃ C, M.Circuit C :=
  by
  simp_rw [Matroid.rk, r_lt_card_iff_dep, dep_iff_supset_circuit, exists_prop,
    and_iff_right (subset_univ _)]

end Circuit

section ClFlat

variable {F F' F₁ F₂ H H₁ H₂ : Set E}

theorem Flat.r_insert_of_not_mem_of_rFin (hF : M.Flat F) (he : e ∉ F) (hfin : M.RFin F) :
    M.R (insert e F) = M.R F + 1 :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis F
  rw [← hF.cl, ← hI.cl, hI.indep.not_mem_cl_iff] at he
  rw [← (hI.insert_basis_insert he.2).card, ← hI.card,
    ncard_insert_of_not_mem he.1 (hI.finite_of_r_fin hfin)]

theorem Flat.r_insert_of_not_mem [FiniteRk M] (hF : M.Flat F) (he : e ∉ F) :
    M.R (insert e F) = M.R F + 1 :=
  hF.r_insert_of_not_mem_of_rFin he (M.to_rFin F)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e «expr ∉ » F) -/
theorem flat_iff_r_lt_r_insert [FiniteRk M] :
    M.Flat F ↔ ∀ (e) (_ : e ∉ F), M.R F < M.R (insert e F) :=
  by
  refine'
    ⟨fun hF e heF => nat.lt_iff_add_one_le.mpr (hF.r_insert_of_not_mem heF).symm.le, fun h =>
      flat_def.mpr fun I X hIF hIX => _⟩
  by_contra' hXF
  obtain ⟨e, heX, heF⟩ := not_subset.mp hXF
  apply (h _ heF).Ne
  rw [← hIF.r_eq_r_insert, hIX.r_eq_r_insert, insert_eq_of_mem heX, ← hIF.r, ← hIX.r]

theorem Flat.not_mem_iff_r_insert_of_rFin (hF : M.Flat F) (hfin : M.RFin F) :
    e ∉ F ↔ M.R (insert e F) = M.R F + 1 :=
  by
  refine' ⟨fun he => hF.r_insert_of_not_mem_of_r_fin he hfin, fun h he => _⟩
  rw [insert_eq_of_mem he, self_eq_add_right] at h
  simpa only using h

theorem Flat.not_mem_iff_r_insert [FiniteRk M] (hF : M.Flat F) :
    e ∉ F ↔ M.R (insert e F) = M.R F + 1 :=
  hF.not_mem_iff_r_insert_of_rFin (M.to_rFin F)

theorem Flat.r_lt_r_of_sSubset_of_rFin (hF : M.Flat F) (hFX : F ⊂ X) (hX : M.RFin X) :
    M.R F < M.R X := by
  obtain ⟨e, heX, heF⟩ := exists_of_ssubset hFX
  rw [Nat.lt_iff_add_one_le, ← hF.r_insert_of_not_mem_of_r_fin heF (hX.subset hFX.subset)]
  exact hX.r_mono (insert_subset.mpr ⟨heX, hFX.subset⟩)

theorem Flat.eq_of_r_le_r_subset_of_rFin (hF : M.Flat F) (hFfin : M.RFin X) (hFX : F ⊆ X)
    (hr : M.R X ≤ M.R F) : F = X :=
  by_contra fun hne => (hF.r_lt_r_of_sSubset_of_rFin (hFX.ssubset_of_ne hne) hFfin).not_le hr

theorem Flat.r_lt_r_of_sSubset [FiniteRk M] (hF : M.Flat F) (hFX : F ⊂ X) : M.R F < M.R X :=
  hF.r_lt_r_of_sSubset_of_rFin hFX (M.to_rFin X)

theorem Flat.eq_of_le_r_subset [FiniteRk M] (hF : M.Flat F) (hFX : F ⊆ X) (hr : M.R X ≤ M.R F) :
    F = X :=
  hF.eq_of_r_le_r_subset_of_rFin (M.to_rFin X) hFX hr

theorem Flat.eq_univ_of_rk_le_r [FiniteRk M] (hF : M.Flat F) (hr : M.rk ≤ M.R F) : F = univ :=
  hF.eq_of_le_r_subset (subset_univ _) hr

theorem RFin.mem_cl_iff_r_insert (hX : M.RFin X) : e ∈ M.cl X ↔ M.R (insert e X) = M.R X := by
  rw [← not_iff_not, ← Ne.def, ← r_insert_eq_add_one_iff_r_ne, ← singleton_union, ←
    r_union_cl_right_eq_r_union, singleton_union,
    (M.flat_of_cl X).not_mem_iff_r_insert_of_rFin hX.to_cl, r_cl]

theorem RFin.not_mem_cl_iff_r_insert (hX : M.RFin X) : e ∉ M.cl X ↔ M.R (insert e X) = M.R X + 1 :=
  by
  rw [hX.mem_cl_iff_r_insert, ← Ne.def]
  refine'
    ⟨r_insert_eq_add_one_of_r_ne, fun h => by
      simp only [h, Ne.def, Nat.succ_ne_self, not_false_iff]⟩

theorem mem_cl_iff_r_insert [FiniteRk M] : e ∈ M.cl X ↔ M.R (insert e X) = M.R X :=
  (M.to_rFin X).mem_cl_iff_r_insert

theorem not_mem_cl_iff_r_insert [FiniteRk M] : e ∉ M.cl X ↔ M.R (insert e X) = M.R X + 1 :=
  (M.to_rFin X).not_mem_cl_iff_r_insert

theorem subset_cl_iff_r_union_eq_r [FiniteRk M] : X ⊆ M.cl Y ↔ M.R (Y ∪ X) = M.R Y :=
  by
  refine'
    ⟨fun h => r_union_eq_of_r_all_insert_le fun e he => by rw [mem_cl_iff_r_insert.mp (h he)],
      fun hu e heX => mem_cl_iff_r_insert.mpr ((M.r_mono (subset_insert _ _)).antisymm' _)⟩
  rw [← hu]
  apply r_mono
  rw [insert_subset]
  simp only [mem_union, subset_union_left, and_true_iff]
  exact Or.inr heX

theorem r_insert_eq_add_one_of_not_mem_cl [FiniteRk M] (h : e ∉ M.cl X) :
    M.R (insert e X) = M.R X + 1 :=
  r_insert_eq_add_one_of_r_ne (h ∘ mem_cl_iff_r_insert.mpr)

theorem not_mem_cl_of_r_insert_gt [FiniteRk M] (h : M.R X < M.R (insert e X)) : e ∉ M.cl X :=
  h.Ne.symm ∘ mem_cl_iff_r_insert.mp

theorem mem_cl_of_r_insert_le [FiniteRk M] (h : M.R (insert e X) ≤ M.R X) : e ∈ M.cl X :=
  mem_cl_iff_r_insert.mpr (h.antisymm (M.r_le_r_insert e X))

theorem r_eq_rk_iff_cl_eq_univ [FiniteRk M] : M.R X = M.rk ↔ M.cl X = univ :=
  ⟨fun h => eq_univ_iff_forall.mpr fun e => mem_cl_of_r_insert_le ((M.r_le_rk _).trans_eq h.symm),
    fun h => by rw [← M.r_cl, h, rk]⟩

theorem not_mem_cl_iff_r_insert_eq_add_one [FiniteRk M] :
    e ∉ M.cl X ↔ M.R (insert e X) = M.R X + 1 :=
  ⟨r_insert_eq_add_one_of_not_mem_cl, fun h =>
    not_mem_cl_of_r_insert_gt
      (by
        rw [h]
        apply lt_add_one)⟩

theorem r_le_iff_cl {n : ℕ} [FiniteRk M] : M.R X ≤ n ↔ ∃ I, X ⊆ M.cl I ∧ I.ncard ≤ n ∧ I.Finite :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    exact ⟨I, hI.subset_cl, by rwa [hI.card], hI.finite⟩
  rintro ⟨I, hXI, hIn⟩
  refine' (M.r_mono hXI).trans _
  rw [r_cl]
  exact (M.r_le_card_of_finite hIn.2).trans hIn.1

theorem le_r_iff_cl {n : ℕ} [FiniteRk M] : n ≤ M.R X ↔ ∀ I, X ⊆ M.cl I → I.Finite → n ≤ I.ncard :=
  by
  cases n; simp
  rw [← not_lt, ← not_iff_not, Classical.not_not, not_forall]
  simp_rw [not_imp, not_le, Nat.lt_succ_iff]
  rw [r_le_iff_cl]
  tauto

theorem Flat.covby_iff_r_of_rFin (hF : M.Flat F) (hFfin : M.RFin F) (hF' : M.Flat F') :
    M.Covby F F' ↔ F ⊆ F' ∧ M.R F' = M.R F + 1 :=
  by
  rw [hF.covby_iff_eq_cl_insert]
  refine' ⟨_, fun h => _⟩
  · rintro ⟨e, he, rfl⟩
    rw [and_iff_right (M.subset_cl_of_subset (subset_insert _ _)), r_cl,
      (hF.not_mem_iff_r_insert_of_r_fin hFfin).mp he]
  have hss : F ⊂ F' :=
    h.1.ssubset_of_ne
      (by
        rintro rfl
        simpa using h.2)
  obtain ⟨e, heF', heF⟩ := exists_of_ssubset hss
  refine' ⟨e, heF, ((M.flat_of_cl _).eq_of_r_le_r_subset_of_rFin _ _ _).symm⟩
  · refine' r_fin_of_r_ne_zero _
    rw [h.2]
    exact Nat.succ_ne_zero _
  · exact hF'.cl_subset_of_subset (insert_subset.mpr ⟨heF', h.1⟩)
  rw [h.2, r_cl, hF.r_insert_of_not_mem_of_r_fin heF hFfin]

theorem Flat.covby_iff_r [FiniteRk M] (hF : M.Flat F) (hF' : M.Flat F') :
    M.Covby F F' ↔ F ⊆ F' ∧ M.R F' = M.R F + 1 :=
  hF.covby_iff_r_of_rFin (M.to_rFin F) hF'

theorem hyperplane_iff_maximal_r [FiniteRk M] :
    M.Hyperplane H ↔ M.R H < M.rk ∧ ∀ X, H ⊂ X → M.R X = M.rk := by
  simp_rw [hyperplane_iff_maximal_cl_ne_univ, lt_rk_iff_ne_rk, Ne.def, ← r_eq_rk_iff_cl_eq_univ]

theorem Hyperplane.r_add_one [FiniteRk M] (hH : M.Hyperplane H) : M.R H + 1 = M.rk :=
  by
  rw [hyperplane_iff_maximal_r] at hH
  obtain rfl | hne := eq_or_ne H univ
  · exact (hH.1.Ne rfl).elim
  obtain ⟨e, he⟩ := (ne_univ_iff_exists_not_mem _).mp hne
  refine' (nat.lt_iff_add_one_le.mp hH.1).antisymm _
  rw [← hH.2 (insert e H) (ssubset_insert he)]
  exact M.r_insert_le_add_one e H

theorem Hyperplane.cast_r [FiniteRk M] (hH : M.Hyperplane H) : (M.R H : ℤ) = M.rk - 1 := by
  simp [← hH.r_add_one]

theorem Flat.hyperplane_of_r_add_one_eq_rk [FiniteRk M] (hF : M.Flat F) (h : M.R F + 1 = M.rk) :
    M.Hyperplane F :=
  by
  rw [hyperplane_iff_maximal_r, ← h, iff_true_intro (lt_add_one (M.r F)), true_and_iff]
  refine' fun X hFX =>
    ((M.r_le_rk X).trans_eq h.symm).antisymm (nat.add_one_le_iff.mpr (hF.r_lt_r_of_ssubset hFX))

theorem hyperplane_iff_flat_r_add_one_eq_r [FiniteRk M] :
    M.Hyperplane H ↔ M.Flat H ∧ M.R H + 1 = M.rk :=
  ⟨fun h => ⟨h.Flat, h.r_add_one⟩, fun h => h.1.hyperplane_of_r_add_one_eq_rk h.2⟩

end ClFlat

section Loop

theorem loop_iff_r : M.Loop e ↔ M.R {e} = 0 :=
  by
  rw [loop_iff_dep, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton]
  refine'
    ⟨fun h => Nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _), fun h h' =>
      Nat.zero_ne_one (h.symm.trans h')⟩
  convert(M.r_le_card_of_finite (finite_singleton e)).lt_of_ne _
  · rw [ncard_singleton]
  rwa [ncard_singleton]

theorem Loop.r (he : M.Loop e) : M.R {e} = 0 :=
  loop_iff_r.mp he

theorem r_eq_zero_iff_subset_loops [FiniteRk M] : M.R X = 0 ↔ X ⊆ M.cl ∅ :=
  (M.to_rFin X).r_eq_zero_iff_subset_loops

theorem r_eq_zero_iff_forall_loop [FiniteRk M] : M.R X = 0 ↔ ∀ e ∈ X, M.Loop e :=
  r_eq_zero_iff_subset_loops

theorem r_eq_zero_of_subset_loops (h : X ⊆ M.cl ∅) : M.R X = 0 := by
  rw [← r_cl, cl_eq_loops_of_subset h, r_cl, r_empty]

theorem nonloop_iff_r : M.Nonloop e ↔ M.R {e} = 1 := by
  rw [← indep_singleton, indep_iff_r_eq_card_of_finite (finite_singleton e), ncard_singleton]

theorem Nonloop.r (he : M.Nonloop e) : M.R {e} = 1 :=
  nonloop_iff_r.mp he

theorem Coloop.r_compl_add_one [FiniteRk M] (he : M.Coloop e) : M.R ({e}ᶜ) + 1 = M.rk :=
  by
  rw [coloop_iff_forall_mem_base] at he
  obtain ⟨I, hI⟩ := M.exists_basis ({e}ᶜ)
  obtain ⟨B, hB, hIB⟩ := hI.indep.subset_basis_of_subset (subset_univ I)
  rw [← base_iff_basis_univ] at hB
  have heI : e ∉ I := fun heI => by simpa using hI.subset heI
  have hIB' : B = insert e I := by
    refine' subset_antisymm _ _
    · rw [← union_singleton, ← inter_union_diff B {e}, union_subset_iff]
      refine'
        ⟨(inter_subset_right _ _).trans (subset_union_right _ _), subset_union_of_subset_left _ _⟩
      rw [hI.eq_of_subset_indep (hB.indep.diff {e}) (subset_diff_singleton hIB heI) _]
      rw [compl_eq_univ_diff]
      exact diff_subset_diff_left (subset_univ _)
    exact insert_subset.mpr ⟨he hB, hIB⟩
  subst hIB'
  rw [← hI.r, hI.indep.r, ← hB.r, hB.indep.r, ncard_insert_of_not_mem heI hI.finite]

theorem coloop_iff_r_compl_add_one_eq [FiniteRk M] : M.Coloop e ↔ M.R ({e}ᶜ) + 1 = M.rk :=
  by
  refine'
    ⟨coloop.r_compl_add_one, fun h =>
      coloop_iff_forall_mem_base.mpr fun B hB => by_contra fun h' => _⟩
  rw [← subset_compl_singleton_iff] at h'
  have hB' := M.r_mono h'
  rw [hB.r, ← h] at hB'
  simpa only [add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero] using hB'

theorem coloop_iff_r_compl_lt [FiniteRk M] : M.Coloop e ↔ M.R ({e}ᶜ) < M.rk :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← h.r_compl_add_one]
    apply lt_add_one
  have he : insert e ({e}ᶜ : Set E) = univ := by
    ext
    simp [em]
  rw [rk, ← he] at h
  rw [coloop_iff_r_compl_add_one_eq, eq_comm, rk, ← he, r_insert_eq_add_one_of_r_ne h.ne.symm]

theorem Coloop.coe_r_compl [FiniteRk M] (he : M.Coloop e) : (M.R ({e}ᶜ) : ℤ) = M.rk - 1 := by
  simp [← he.r_compl_add_one]

end Loop

section FlatOfR

variable {F F' P L : Set E}

/-- `M.flat_of_r k F` means that `F` is a flat in `r` with finite rank `k`. -/
def FlatOfR (M : Matroid E) (k : ℕ) (F : Set E) :=
  M.Flat F ∧ M.R F = k ∧ M.RFin F

theorem FlatOfR.flat (h : M.FlatOfR k F) : M.Flat F :=
  h.1

theorem FlatOfR.r (h : M.FlatOfR k F) : M.R F = k :=
  h.2.1

theorem FlatOfR.rFin (h : M.FlatOfR k F) : M.RFin F :=
  h.2.2

theorem Flat.flatOfR_of_ne_zero (hF : M.Flat F) (hk : M.R F ≠ 0) : M.FlatOfR (M.R F) F :=
  ⟨hF, rfl, rFin_of_r_ne_zero hk⟩

theorem Flat.flatOfR_of_ne_zero' (hF : M.Flat F) (hr : M.R F = k) (hk : k ≠ 0) :
    M.FlatOfR (M.R F) F :=
  hF.flatOfR_of_ne_zero
    (by
      subst hr
      assumption)

theorem FlatOfR.nonempty (hF : M.FlatOfR k F) (hk : k ≠ 0) : F.Nonempty :=
  nonempty_of_r_nonzero (ne_of_eq_of_ne hF.R hk)

@[simp]
theorem flatOfR_zero_iff_loops : M.FlatOfR 0 F ↔ F = M.cl ∅ :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨I, hI⟩ := M.exists_basis F
    have hc := hI.card
    rw [h.r, ncard_eq_zero (hI.finite_of_r_fin h.r_fin)] at hc
    subst hc
    rw [← h.flat.cl, hI.cl]
  rintro rfl
  exact ⟨M.flat_of_cl _, by simp, M.r_fin_empty.to_cl⟩

theorem loops_flatOfR_zero (M : Matroid E) : M.FlatOfR 0 (M.cl ∅) := by
  rw [flat_of_r_zero_iff_loops]

theorem FlatOfR.covby_iff (hF : M.FlatOfR k F) : M.Covby F F' ↔ M.FlatOfR (k + 1) F' ∧ F ⊆ F' :=
  by
  refine'
    (em (M.flat F')).symm.elim (fun hF' => iff_of_false (mt covby.flat_right hF') _) fun hF' => _
  · exact mt (fun h => h.1.Flat) hF'
  have hr := hF.r; subst hr
  simp_rw [hF.flat.covby_iff_r_of_r_fin hF.r_fin hF', flat_of_r, and_comm', and_congr_right_iff, ←
    and_assoc', iff_and_self, and_iff_right hF']
  refine' fun h hF' => r_fin_of_r_ne_zero _
  rw [hF']
  simp

theorem FlatOfR.flatOfR_add_one_of_covby (hF : M.FlatOfR k F) (hFF' : M.Covby F F') :
    M.FlatOfR (k + 1) F' := by
  rw [hF.covby_iff] at hFF'
  exact hFF'.1

/-- A `point` is a rank-one flat -/
def Point (M : Matroid E) (P : Set E) :=
  M.FlatOfR 1 P

/-- A `line` is a rank-two flat -/
def Line (M : Matroid E) (L : Set E) :=
  M.FlatOfR 2 L

/-- A `plane` is a rank-three flat -/
def Plane (M : Matroid E) (P : Set E) :=
  M.FlatOfR 3 P

theorem Point.nonempty (hP : M.Point P) : P.Nonempty :=
  FlatOfR.nonempty hP one_ne_zero

theorem Line.nonempty (hL : M.line L) : L.Nonempty :=
  FlatOfR.nonempty hL two_ne_zero

theorem Plane.nonempty (hP : M.Plane P) : P.Nonempty :=
  FlatOfR.nonempty hP three_pos.Ne.symm

theorem Nonloop.cl_point (he : M.Nonloop e) : M.Point (M.cl {e}) :=
  by
  rw [point, ← ncard_singleton e, ← he.indep.r, ← r_cl]
  exact
    (M.flat_of_cl _).flatOfR_of_ne_zero
      (by
        rw [r_cl, he.indep.r]
        simp)

theorem Point.diff_loops_nonempty (hP : M.Point P) : (P \ M.cl ∅).Nonempty :=
  nonempty_of_r_nonzero
    (by
      rw [← r_cl, cl_diff_loops_eq_cl, r_cl, hP.r]
      exact one_ne_zero)

theorem Point.exists_eq_cl_nonloop (hP : M.Point P) : ∃ e, M.Nonloop e ∧ P = M.cl {e} :=
  by
  obtain ⟨I, hI⟩ := M.exists_basis P
  have hc := hI.card
  rw [hP.r, ncard_eq_one] at hc
  obtain ⟨e, rfl⟩ := hc
  use e
  rw [hI.cl, hP.flat.cl, and_iff_left rfl, nonloop_iff_r, hI.r, hP.r]

theorem Point.eq_cl_nonloop (hP : M.Point P) (heP : e ∈ P) (he : M.Nonloop e) : P = M.cl {e} :=
  by
  obtain ⟨I, hI, heI⟩ := he.indep.subset_basis_of_subset (singleton_subset_iff.mpr heP)
  have hc := hI.card
  rw [hP.r, ncard_eq_one] at hc
  obtain ⟨e', rfl⟩ := hc
  simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heI
  rw [← hP.flat.cl, ← hI.cl, heI]

/-- The set of elements that span a point are precisely its nonloop members -/
theorem Point.eq_cl_singleton_iff (h : M.Point P) : M.cl {e} = P ↔ e ∈ P ∧ M.Nonloop e :=
  by
  simp only [nonloop, loop, ← mem_diff, mem_preimage, mem_singleton_iff]
  refine' ⟨_, fun hP => _⟩
  · rintro rfl
    refine' ⟨M.mem_cl_self e, fun he : M.loop e => he.dep _⟩
    have hr := h.r
    rwa [r_cl, ← ncard_singleton e, ← indep_iff_r_eq_card_of_finite (finite_singleton e)] at hr
  have he : M.nonloop e := hP.2
  obtain ⟨J, hJ, heJ⟩ := he.indep.subset_basis_of_subset (singleton_subset_iff.mpr hP.1)
  have hJcard := hJ.card
  rw [h.r, ncard_eq_one] at hJcard
  obtain ⟨e', rfl⟩ := hJcard
  simp only [subset_singleton_iff, mem_singleton_iff, forall_eq] at heJ; subst heJ
  rw [← h.flat.cl, hJ.cl]

theorem point_iff_loops_covby : M.Point P ↔ M.Covby (M.cl ∅) P :=
  by
  rw [flat_of_r.covby_iff M.loops_flat_of_r_zero, zero_add, point, iff_self_and]
  exact fun h => h.flat.loops_subset

end FlatOfR

section FromAxioms

/-- There doesn't seem to be a nice way to axiomatize finite-rank matroids on infinite ground sets
  without a 'bases for sets exist'-type axiom. A troublesome example is the rank-1 non-matroid where
  the only rank-1 set is the (infinite) ground set, which satisfies finite versions of submodularity
  but has no nonempty independent sets.  -/
theorem card_le_r_of_card_le_r_of_subset [Finite E] (r : Set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
    (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) {I J : Set E} (hJ : J.ncard ≤ r J)
    (hIJ : I ⊆ J) : I.ncard ≤ r I :=
  by
  have hsm := r_submod I (J \ I)
  rw [inter_diff_self, union_diff_self, union_eq_self_of_subset_left hIJ] at hsm
  linarith [r_le_card (J \ I), ncard_diff_add_ncard_eq_ncard hIJ]

theorem r_eq_r_of_maximal_indep [Finite E] (r : Set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
    (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y)
    (I X : Set E) (hI : I ∈ maximals (· ⊆ ·) { J | J ⊆ X ∧ J.ncard ≤ r J }) : r I = r X :=
  by
  obtain ⟨J, ⟨hJX, hIJ, hJ⟩, hJmax⟩ :=
    (to_finite X).maximals_nonempty_of_exists (fun J => I ⊆ J ∧ r J ≤ r I) hI.1.1
      ⟨subset.rfl, rfl.le⟩
  obtain rfl | hss := hJX.eq_or_ssubset
  · exact hJ.antisymm' (r_mono hIJ)
  obtain ⟨e, heX, heJ⟩ := exists_of_ssubset hss
  have hsm := r_submod (insert e I) J
  rw [insert_union, union_eq_self_of_subset_left hIJ] at hsm
  have heI : r (insert e I) ≤ r I :=
    by
    refine'
      (em (e ∈ I)).elim (fun heI => by rw [insert_eq_of_mem heI]) fun heI =>
        le_of_not_lt fun hlt => _
    refine' heI (hI.2 ⟨insert_subset.mpr ⟨heX, hI.1.1⟩, _⟩ (subset_insert e I) (mem_insert e I))
    linarith [hI.1.2, nat.lt_iff_add_one_le.mp hlt, ncard_insert_of_not_mem heI]
  have heJ : r I + 1 ≤ r (insert e J) :=
    by
    refine' nat.add_one_le_iff.mpr (lt_of_not_le fun hle => heJ _)
    exact
      hJmax ⟨insert_subset.mpr ⟨heX, hss.subset⟩, ⟨hIJ.trans (subset_insert e J), hle⟩⟩
        (subset_insert e J) (mem_insert e J)
  linarith [r_mono (subset_inter (subset_insert e I) hIJ)]

def matroidOfR [Finite E] (r : Set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
    (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
    Matroid E :=
  matroidOfIndepOfFinite (fun I => I.ncard ≤ r I)
    (by
      use ∅
      simp)
    (fun I J => card_le_r_of_card_le_r_of_subset r ‹_› ‹_›)
    (by
      intro I J hI hJ hIJ
      by_contra' h'
      have con := r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_› I (I ∪ J) ⟨⟨subset_union_left _ _, hI⟩, _⟩
      ·
        exact
          (r_le_card I).not_lt
            ((hIJ.trans_le (hJ.trans (r_mono (subset_union_right I J)))).trans_eq Con.symm)
      exact fun K hK hIK e heK =>
        by_contra fun heI =>
          (card_le_r_of_card_le_r_of_subset r ‹_› ‹_› hK.2 (insert_subset.mpr ⟨heK, hIK⟩)).not_lt
            (h' _ ((hK.1 heK).elim (False.elim ∘ heI) id) heI))

@[simp]
theorem matroidOfR_apply [Finite E] (r : Set E → ℕ) (r_le_card : ∀ X, r X ≤ X.ncard)
    (r_mono : ∀ ⦃X Y⦄, X ⊆ Y → r X ≤ r Y) (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) :
    (matroidOfR r r_le_card r_mono r_submod).R = r :=
  by
  ext X
  obtain ⟨I, hI⟩ := (matroid_of_r r ‹_› ‹_› ‹_›).exists_basis X
  rw [← hI.card]
  simp_rw [matroid_of_r, basis_iff, matroid_of_indep_of_finite_apply] at hI
  rw [hI.1.antisymm (r_le_card I), r_eq_r_of_maximal_indep r ‹_› ‹_› ‹_›]
  exact ⟨⟨hI.2.1, hI.1⟩, fun J hJ hIJ => (hI.2.2 J hJ.2 hIJ hJ.1).symm.Subset⟩

/-- Construction of a matroid from an `int`-valued rank function that is everywhere nonnegative,
  rather than a `nat`-valued one. Useful for defining matroids whose rank function involves
  subtraction. -/
def matroidOfIntR [Finite E] (r : Set E → ℤ) (r_nonneg : ∀ X, 0 ≤ r X)
    (r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
    (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) : Matroid E :=
  matroidOfR (Int.natAbs ∘ r)
    (fun X => by
      zify
      convert r_le_card X
      rw [abs_eq_self]
      apply r_nonneg)
    (fun X Y hXY => by
      zify
      convert r_mono X Y hXY
      all_goals rw [abs_eq_self]; apply r_nonneg)
    fun X Y => by
    zify
    convert r_submod X Y
    all_goals rw [abs_eq_self]; apply r_nonneg

@[simp]
theorem matroidOfIntR_apply [Finite E] (r : Set E → ℤ) (r_nonneg : ∀ X, 0 ≤ r X)
    (r_le_card : ∀ X, r X ≤ X.ncard) (r_mono : ∀ X Y, X ⊆ Y → r X ≤ r Y)
    (r_submod : ∀ X Y, r (X ∩ Y) + r (X ∪ Y) ≤ r X + r Y) (X : Set E) :
    ((matroidOfIntR r r_nonneg r_le_card r_mono r_submod).R X : ℤ) = r X := by
  simpa [matroid_of_int_r] using r_nonneg _

end FromAxioms

section Dual

variable [Finite E]

theorem coindep_iff_r : M.Coindep X ↔ M.R (Xᶜ) = M.rk :=
  by
  rw [coindep_iff_disjoint_base]
  constructor
  · rintro ⟨B, hB, hBX⟩
    refine' le_antisymm (M.r_le_rk _) _
    rw [← subset_compl_iff_disjoint_left] at hBX
    rw [← hB.r]
    exact M.r_mono hBX
  intro hr
  obtain ⟨B, hB⟩ := M.exists_basis (Xᶜ)
  refine' ⟨B, hB.indep.base_of_rk_le_card _, subset_compl_iff_disjoint_left.mp hB.subset⟩
  rw [← hB.indep.r, hB.r, hr]

theorem dual_r_add_rk_eq (M : Matroid E) (X : Set E) : M﹡.R X + M.rk = ncard X + M.R (Xᶜ) :=
  by
  set r' : Set E → ℤ := fun X => X.ncard + M.r (Xᶜ) - M.rk with hr'
  have hr'_nonneg : ∀ X, 0 ≤ r' X := by
    intro X
    simp_rw [hr']
    linarith [M.rk_le_card_add_r_compl X]
  have hr'_mono : ∀ X Y, X ⊆ Y → r' X ≤ r' Y :=
    by
    intro X Y hXY
    simp_rw [hr']
    linarith [M.r_add_card_le_r_add_card_of_subset (compl_subset_compl.mpr hXY),
      ncard_add_ncard_compl X, ncard_add_ncard_compl Y]
  have hr'_le_card : ∀ X, r' X ≤ X.ncard := by
    intro X
    simp_rw [hr']
    linarith [M.r_le_rk (Xᶜ)]
  have hr'_submod : ∀ X Y, r' (X ∩ Y) + r' (X ∪ Y) ≤ r' X + r' Y :=
    by
    intro X Y
    simp_rw [hr', compl_inter, compl_union]
    linarith [ncard_inter_add_ncard_union X Y, M.r_submod (Xᶜ) (Yᶜ)]
  set M' := matroid_of_int_r r' hr'_nonneg hr'_le_card hr'_mono hr'_submod with hM'
  have hM'M : M' = M﹡ := by
    refine' eq_of_indep_iff_indep_forall fun I => _
    rw [indep_iff_r_eq_card, dual_indep_iff_coindep, coindep_iff_r]
    zify
    simp_rw [hM', matroid_of_int_r_apply, hr']
    refine' ⟨fun h => _, fun h => _⟩
    all_goals simp only at h; linarith
  rw [← hM'M]
  zify
  simp_rw [hM', matroid_of_int_r_apply, hr']
  ring

theorem dual_r_cast_eq (M : Matroid E) (X : Set E) : (M﹡.R X : ℤ) = ncard X + M.R (Xᶜ) - M.rk := by
  linarith [M.dual_r_add_rk_eq X]

end Dual

end Matroid

