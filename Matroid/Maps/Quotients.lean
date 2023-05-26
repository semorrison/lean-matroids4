import Matroid.Rank
import Mathlib.Tactic.Tfae

open Classical

open Set List

namespace Matroid

variable {E : Type _} {X Y I C B F : Set E} {N M : Matroid E} {e f : E}

section WeakImage

-- `M` is a weak image of `N` if independence in `N` implies independence in `M`
def WeakImage (N M : Matroid E) :=
  ∀ I, N.indep I → M.indep I

-- mathport name: «expr ≤w »
infixl:75 " ≤w " => WeakImage

theorem weakImage_def : N ≤w M ↔ ∀ I, N.indep I → M.indep I :=
  Iff.rfl

theorem Indep.weakImage (hI : N.indep I) (h : N ≤w M) : M.indep I :=
  h _ hI

theorem WeakImage.finiteRk [FiniteRk M] (h : N ≤w M) : FiniteRk N :=
  by
  obtain ⟨B, hB⟩ := N.exists_base
  exact hB.finite_rk_of_finite (h B hB.indep).Finite

theorem weakImage_iff_r [FiniteRk N] [FiniteRk M] : N ≤w M ↔ ∀ X, N.R X ≤ M.R X :=
  by
  simp_rw [r_le_iff, le_r_iff]
  refine' ⟨fun h X I hIX hIN => ⟨I, hIX, h _ hIN, rfl⟩, fun h I hI => _⟩
  obtain ⟨J, hJI, hJ, hJ'⟩ := h I I subset.rfl hI
  rwa [← eq_of_subset_of_ncard_le hJI hJ'.symm.le hI.finite]

theorem WeakImage.r_le [FiniteRk N] [FiniteRk M] (h : N ≤w M) (X : Set E) : N.R X ≤ M.R X :=
  weakImage_iff_r.mp h X

theorem weakImage_iff_dep : N ≤w M ↔ ∀ X, ¬M.indep X → ¬N.indep X := by
  simp_rw [weak_image_def, not_imp_not]

theorem WeakImage.dep (h : N ≤w M) (hX : ¬M.indep X) : ¬N.indep X :=
  weakImage_iff_dep.mp h _ hX

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (C' «expr ⊆ » C) -/
theorem weakImage_iff_circuit : N ≤w M ↔ ∀ C, M.Circuit C → ∃ (C' : _)(_ : C' ⊆ C), N.Circuit C' :=
  by
  simp_rw [weak_image_iff_dep, dep_iff_supset_circuit]
  refine' ⟨fun h => fun C hC => _, fun h => fun X hX => _⟩
  · apply h
    exact ⟨C, subset_refl _, hC⟩
  rcases hX with ⟨C, ⟨h', h''⟩⟩
  rcases h C h'' with ⟨C', h1, h2⟩
  refine' ⟨C', h1.trans h', h2⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (C' «expr ⊆ » C) -/
theorem Circuit.supset_circuit_of_weakImage (hC : M.Circuit C) (h : N ≤w M) :
    ∃ (C' : _)(_ : C' ⊆ C), N.Circuit C' :=
  weakImage_iff_circuit.mp h _ hC

theorem RFin.weakImage (hX : M.RFin X) (h : N ≤w M) : N.RFin X :=
  by
  obtain ⟨I, hI⟩ := N.exists_basis X
  obtain ⟨J, hJ, hIJ⟩ := (hI.indep.weak_image h).subset_basis_of_subset hI.subset
  exact hI.r_fin_of_finite ((hJ.finite_of_r_fin hX).Subset hIJ)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (C' «expr ⊆ » C) -/
theorem weakImage_tFAE [FiniteRk N] [FiniteRk M] :
    TFAE
      [N ≤w M, ∀ X, N.R X ≤ M.R X, ∀ X, N.indep X → M.indep X, ∀ X, ¬M.indep X → ¬N.indep X,
        ∀ C, M.Circuit C → ∃ (C' : _)(_ : C' ⊆ C), N.Circuit C'] :=
  by
  tfae_have 1 ↔ 2; apply weak_image_iff_r
  tfae_have 1 ↔ 3; apply weak_image_def
  tfae_have 1 ↔ 4; apply weak_image_iff_dep
  tfae_have 1 ↔ 5; apply weak_image_iff_circuit
  tfae_finish

theorem WeakImage.r_eq_zero_of_r_eq_zero [FiniteRk N] [FiniteRk M] (h : N ≤w M) (hX : M.R X = 0) :
    N.R X = 0 :=
  Nat.eq_zero_of_le_zero ((WeakImage.r_le h X).trans_eq hX)

theorem Loop.weakImage (he : M.Loop e) (h : N ≤w M) : N.Loop e :=
  not_nonloop_iff.mp fun hnl => h.dep he.dep hnl.indep

theorem nonloop_of_weakImage_nonloop (h : N ≤w M) {e : E} (he : ¬N.Loop e) : ¬M.Loop e := fun he' =>
  he (he'.WeakImage h)

instance (E : Type _) : IsPartialOrder (Matroid E) (· ≤w ·)
    where
  refl I hI := id
  trans M₀ M₁ M₂ h h' I hI := h' I (h I hI)
  antisymm M M' h h' := eq_of_indep_iff_indep_forall fun I => ⟨fun hI => h I hI, fun hI => h' I hI⟩

end WeakImage

section Quotient

/-- a quotient of M is a matroid N for which rank differences of nested pairs in N are at most
the corresponding rank differences in M. This is equivalent to the existence of a matroid P for
which M is a deletion of P and N is a contraction of P, but we do not show this equivalence here.
-/
def IsQuotient (N M : Matroid E) :=
  ∀ X, M.cl X ⊆ N.cl X

-- mathport name: «expr ≼ »
infixl:75 " ≼ " => IsQuotient

theorem IsQuotient.cl_subset (h : N ≼ M) (X : Set E) : M.cl X ⊆ N.cl X :=
  h X

theorem IsQuotient.weakImage (h : N ≼ M) : N ≤w M :=
  by
  refine' fun X hX => by_contra fun h' => _
  obtain ⟨C, hCX, hC⟩ := dep_iff_supset_circuit.mp h'
  obtain ⟨e, heC⟩ := hC.nonempty
  have he := (hC.subset_cl_diff_singleton e).trans (h (C \ {e}))
  exact (cl_subset_cl he).not_ssubset ((hX.subset hCX).cl_diff_singleton_sSubset heC)

theorem IsQuotient.r_le_r_of_subset [FiniteRk M] (h : N ≼ M) (hXY : X ⊆ Y) :
    (N.R Y : ℤ) - N.R X ≤ M.R Y - M.R X :=
  by
  haveI := h.weak_image.finite_rk
  obtain ⟨IM, hIM⟩ := M.exists_basis X
  obtain ⟨JM, hJM, hIJM⟩ := hIM.indep.subset_basis_of_subset (hIM.subset.trans hXY)
  obtain ⟨IN, hIN⟩ := N.exists_basis IM
  obtain ⟨JN, hJN, hIJN⟩ := hIN.indep.subset_basis_of_subset (subset_union_left IN (JM \ IM))
  have hINX : N.basis IN X :=
    by
    refine' hIN.indep.basis_of_subset_cl (hIN.subset.trans hIM.subset) _
    rw [hIN.cl]
    refine' subset_trans hIM.subset_cl (h _)
  have hJNY : N.basis JN Y :=
    by
    refine' hJN.indep.basis_of_subset_cl (hJN.subset.trans _) _
    ·
      exact
        union_subset (hIN.subset.trans (hIJM.trans hJM.subset))
          ((diff_subset JM _).trans hJM.subset)
    rw [hJN.cl, ← cl_union_cl_left_eq_cl_union, hIN.cl, cl_union_cl_left_eq_cl_union,
      union_diff_self, union_eq_right_iff_subset.mpr hIJM]
    exact hJM.subset_cl.trans (h _)
  rw [← hINX.card, ← hJNY.card, ← hJM.card, ← hIM.card, ←
    ncard_diff_add_ncard_eq_ncard hIJM hJM.finite, ← ncard_diff_add_ncard_eq_ncard hIJN hJN.finite,
    Nat.cast_add, Nat.cast_add, add_tsub_cancel_right, add_tsub_cancel_right, Nat.cast_le]
  refine' ncard_le_of_subset _ (hJM.finite.diff _)
  rw [diff_subset_iff]
  exact hJN.subset

theorem isQuotient_iff_r [Finite E] : N ≼ M ↔ ∀ X Y, X ⊆ Y → (N.R Y : ℤ) - N.R X ≤ M.R Y - M.R X :=
  by
  refine' ⟨fun h X Y hXY => h.r_le_r_of_subset hXY, fun h Z e he => _⟩
  have hle := h _ _ (subset_insert e Z)
  rw [mem_cl_iff_r_insert.mp he, sub_self, sub_le_iff_le_add, zero_add, Nat.cast_le] at hle
  apply mem_cl_of_r_insert_le hle

theorem Indep.quotient (hI : N.indep I) (h : N ≼ M) : M.indep I :=
  hI.WeakImage h.WeakImage

-- TODO : prove without rank (or with relative rank)
theorem quotient_iff_dual_quotient [Finite E] : N ≼ M ↔ M﹡ ≼ N﹡ :=
  by
  suffices h' : ∀ N M : Matroid E, N ≼ M → M﹡ ≼ N﹡
  exact ⟨fun h => h' _ _ h, fun h => by convert h' _ _ h <;> rw [dual_dual]⟩
  simp_rw [is_quotient_iff_r, dual_r_cast_eq]
  intro N M h X Y hXY
  have := h _ _ (compl_subset_compl.mpr hXY)
  linarith

theorem isQuotient_iff_flat : N ≼ M ↔ ∀ F, N.Flat F → M.Flat F :=
  by
  rw [is_quotient]
  refine' ⟨fun h F hNF => _, fun h => _⟩
  · refine' flat_iff_cl_self.mpr ((M.subset_cl _).antisymm' _)
    have hcl := h F
    rwa [hNF.cl] at hcl
  simp_rw [N.cl_def, subset_sInter_iff, mem_set_of_eq, and_imp]
  exact fun X F hF hXF => (h _ hF).cl_subset_of_subset hXF

theorem Flat.quotient (hF : N.Flat F) (h : N ≼ M) : M.Flat F :=
  (isQuotient_iff_flat.mp h) F hF

theorem quotient_tFAE [Finite E] :
    TFAE
      [N ≼ M, ∀ F, N.Flat F → M.Flat F, ∀ X Y, X ⊆ Y → (N.R Y : ℤ) - N.R X ≤ M.R Y - M.R X,
        ∀ X, M.cl X ⊆ N.cl X, M.dual ≼ N.dual] :=
  by
  tfae_have 1 ↔ 3; exact is_quotient_iff_r
  tfae_have 1 ↔ 2; exact is_quotient_iff_flat
  tfae_have 1 ↔ 4; rfl
  tfae_have 1 ↔ 5; exact quotient_iff_dual_quotient
  tfae_finish

theorem quotient_iff_cl : N ≼ M ↔ ∀ X, M.cl X ⊆ N.cl X :=
  Iff.rfl

theorem eq_of_quotient_of_rk_eq_rk [Finite E] (h : N ≼ M) (hr : N.rk = M.rk) : N = M :=
  by
  refine' eq_of_r_eq_r_forall _
  by_contra' h'
  obtain ⟨S, hS, hmax⟩ := finite.exists_maximal _ h'
  apply hS
  obtain ⟨e, heS⟩ :=
    (ne_univ_iff_exists_not_mem S).mp
      (by
        rintro rfl
        exact hS hr)
  have hi : M.r (insert e S) = N.r (insert e S) :=
    by
    by_contra hi
    exact (ssubset_insert heS).Ne (hmax _ (Ne.symm hi) (subset_insert _ _))
  rw [is_quotient_iff_r] at h
  have h1 := h _ _ (subset_insert e S)
  have h2 := h _ _ (empty_subset S)
  rw [hi] at h1
  simp_rw [r_empty, Nat.cast_zero] at h2
  zify
  linarith

end Quotient

end Matroid

