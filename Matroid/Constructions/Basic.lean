import Matroid.Maps.Quotients
import Matroid.Simple

/-
Basic matroid constructions; free/loopy matroids, truncation, dual, etc.
-/
/-
Basic matroid constructions; free/loopy matroids, truncation, dual, etc.
-/
open Classical

open Set

namespace Matroid

noncomputable section

section FreeLoopy

variable {E : Type _} {X I B : Set E} {e f : E} {r s t : ℕ} {M : Matroid E}

/-- The matroid whose only basis is empty -/
def loopyOn (E : Type _) : Matroid E :=
  matroidOfExistsFiniteBase (fun B => B = ∅) ⟨_, rfl, finite_empty⟩ fun B B' hB hB' a ha =>
    by
    rw [hB] at ha
    exact (not_mem_empty _ ha.1).elim

instance : FiniteRk (loopyOn E) := by
  rw [loopy_on]
  infer_instance

/-- The matroid whose only basis is the whole ground set -/
def freeOn (E : Type _) : Matroid E :=
  loopyOn E﹡

@[simp]
theorem freeOn.dual (E : Type _) : freeOn E﹡ = loopyOn E := by rw [free_on, dual_dual]

@[simp]
theorem loopyOn.dual (E : Type _) : loopyOn E﹡ = freeOn E := by rw [← free_on.dual, dual_dual]

@[simp]
theorem loopyOn.base_iff_empty : (loopyOn E).base B ↔ B = ∅ :=
  Iff.rfl

@[simp]
theorem loopyOn.indep_iff_empty : (loopyOn E).indep I ↔ I = ∅ := by
  simp_rw [indep_iff_subset_base, loopy_on.base_iff_empty, exists_eq_left, subset_empty_iff]

@[simp]
theorem freeOn.base_iff_univ : (freeOn E).base B ↔ B = univ := by
  rw [free_on, dual.base_iff, loopy_on.base_iff_empty, compl_empty_iff]

@[simp]
theorem freeOn.univ_base (E : Type _) : (freeOn E).base univ :=
  freeOn.base_iff_univ.mpr rfl

@[simp]
theorem loopyOn.empty_base (E : Type _) : (loopyOn E).base ∅ :=
  loopyOn.base_iff_empty.mpr rfl

@[simp]
theorem freeOn.indep (I : Set E) : (freeOn E).indep I :=
  (freeOn.univ_base E).indep.Subset (subset_univ _)

@[simp]
theorem univ_indep_iff_eq_freeOn : M.indep univ ↔ M = freeOn E :=
  ⟨fun h => eq_of_indep_iff_indep_forall fun I => by simp [h.subset (subset_univ _)],
    by
    rintro rfl
    exact free_on.indep _⟩

@[simp]
theorem univ_base_iff_freeOn : M.base univ ↔ M = freeOn E :=
  ⟨fun h => univ_indep_iff_eq_freeOn.mp h.indep,
    by
    rintro rfl
    simp⟩

@[simp]
theorem freeOn.r_eq (X : Set E) : (freeOn E).R X = X.ncard := by
  rw [← (free_on.indep X).basis_self.card]

@[simp]
theorem freeOn.rk_eq (E : Type _) : (freeOn E).rk = Nat.card E := by
  rw [rk_def, free_on.r_eq, ncard_univ]

@[simp]
theorem empty_base_iff_loopyOn : M.base ∅ ↔ M = loopyOn E := by
  rw [← compl_compl (∅ : Set E), ← dual.base_iff, compl_empty, univ_base_iff_free_on, ←
    loopy_on.dual, dual_inj_iff]

@[simp]
theorem freeOn.cl (X : Set E) : (freeOn E).cl X = X :=
  (subset_cl _ _).antisymm' fun e he => (freeOn.indep _).mem_cl_iff.mp he (freeOn.indep _)

@[simp]
theorem freeOn.nonloop (e : E) : (freeOn E).Nonloop e :=
  Indep.nonloop (freeOn.indep _)

@[simp]
theorem loopyOn.loop (e : E) : (loopyOn E).Loop e := by
  simp_rw [loop_iff_dep, loopy_on.indep_iff_empty, singleton_ne_empty, not_false_iff]

@[simp]
theorem loopyOn.cl (X : Set E) : (loopyOn E).cl X = univ :=
  by
  refine' eq_univ_of_subset (cl_subset _ (empty_subset X)) (eq_univ_of_forall _)
  simp_rw [← loop_iff_mem_cl_empty]
  exact loopy_on.loop

theorem univ_loops_iff_loopyOn : M.cl ∅ = univ ↔ M = loopyOn E :=
  by
  refine'
    ⟨fun h => eq_of_indep_iff_indep_forall fun I => _,
      by
      rintro rfl
      simp⟩
  simp only [loopy_on.indep_iff_empty]
  refine'
    ⟨fun hI => _, by
      rintro rfl
      simp⟩
  have hdj := hI.disjoint_loops
  rwa [h, disjoint_univ] at hdj

theorem loopy_iff_univ_r_zero [Finite E] : M = loopyOn E ↔ M.R univ = 0 :=
  by
  rw [← univ_loops_iff_loopy_on]
  refine'
    ⟨fun h => by
      rw [← h]
      simp, fun h => _⟩
  rwa [r_eq_zero_iff_subset_loops, univ_subset_iff] at h

end FreeLoopy

section Truncation

variable {E : Type _} {s t : ℕ} {e : E} {I X : Set E} {M : Matroid E}

/-- Truncate a matroid to rank `t`. Every rank above `t` drops to `t`. -/
def tr {E : Type _} (M : Matroid E) (t : ℕ) : Matroid E :=
  matroidOfIndepOfBdd (fun I => M.indep I ∧ I.Finite ∧ I.ncard ≤ t) (by simp)
    (fun I J hJ hIJ =>
      ⟨hJ.1.Subset hIJ, hJ.2.1.Subset hIJ, (ncard_le_of_subset hIJ hJ.2.1).trans hJ.2.2⟩)
    (by
      rintro I B ⟨hI, hIfin, hIc⟩ hInb hB
      obtain hle | hlt := le_or_lt B.ncard I.ncard
      · refine'
          False.elim
            (hInb
              ⟨⟨hI, hIfin, hIc⟩, fun K hK hIK =>
                hIK.ssubset_or_eq.elim (fun hss => False.elim _) fun h => h.symm.subset⟩)
        obtain ⟨e, heK, heB, hei⟩ :=
          hB.1.1.augment_of_finite hK.1 hB.1.2.1 (hle.trans_lt (ncard_lt_ncard hss hK.2.1))
        refine' heB (hB.2 ⟨hei, hB.1.2.1.insert e, _⟩ (subset_insert _ _) (mem_insert _ _))
        rw [ncard_insert_of_not_mem heB hB.1.2.1, Nat.add_one_le_iff]
        exact hle.trans_lt ((ncard_lt_ncard hss hK.2.1).trans_le hK.2.2)
      obtain ⟨e, heB, heI, hi⟩ := hI.augment_of_finite hB.1.1 hIfin hlt
      refine' ⟨e, ⟨heB, heI⟩, hi, hIfin.insert e, (ncard_insert_le _ _).trans _⟩
      rw [Nat.add_one_le_iff]
      exact hlt.trans_le hB.1.2.2)
    ⟨t, fun I => And.right⟩

instance {E : Type _} {M : Matroid E} {t : ℕ} : FiniteRk (M.tr t) :=
  by
  rw [tr]
  infer_instance

theorem tr.indep_iff' : (M.tr t).indep I ↔ M.indep I ∧ I.Finite ∧ I.ncard ≤ t := by simp [tr]

theorem Indep.indep_of_tr_indep (hI : (M.tr t).indep I) : M.indep I :=
  by
  rw [tr.indep_iff'] at hI
  exact hI.1

@[simp]
theorem tr.indep_iff [FiniteRk M] : (M.tr t).indep I ↔ M.indep I ∧ I.ncard ≤ t :=
  by
  rw [tr.indep_iff']
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.Finite, h.2⟩⟩

theorem Nonloop.nonloop_tr_of_ne_zero (he : M.Nonloop e) (ht : t ≠ 0) : (M.tr t).Nonloop e :=
  by
  rw [← indep_singleton, tr.indep_iff', indep_singleton, ncard_singleton, Nat.succ_le_iff,
    pos_iff_ne_zero]
  exact ⟨he, finite_singleton e, ht⟩

theorem tr.nonloop_iff (ht : t ≠ 0) : (M.tr t).Nonloop e ↔ M.Nonloop e :=
  ⟨fun h => indep_singleton.mp (indep_singleton.mpr h).indep_of_tr_indep, fun h =>
    h.nonloop_tr_of_ne_zero ht⟩

@[simp]
theorem tr.r_eq (M : Matroid E) [FiniteRk M] (t : ℕ) (X : Set E) : (M.tr t).R X = min t (M.R X) :=
  by
  refine' le_antisymm (r_le_iff.mpr fun I hIX hI => _) (le_r_iff.mpr _)
  · rw [tr.indep_iff] at hI
    refine' le_min hI.2 _
    rw [← hI.1.R]
    exact M.r_mono hIX
  obtain ⟨J, hJ⟩ := M.exists_basis X
  obtain hle | hlt := le_or_lt J.ncard t
  · refine' ⟨J, hJ.subset, tr.indep_iff.mpr ⟨hJ.indep, hle⟩, _⟩
    rw [hJ.card, eq_comm, min_eq_right]
    rwa [← hJ.card]
  obtain ⟨I, hIJ, rfl⟩ := exists_smaller_set _ _ hlt.le
  refine' ⟨I, hIJ.trans hJ.subset, tr.indep_iff.mpr ⟨hJ.indep.subset hIJ, rfl.le⟩, _⟩
  rw [eq_comm, min_eq_left]
  rw [← hJ.card]
  exact hlt.le

theorem tr.base_iff' (h_rk : t ≤ M.rk ∨ M.InfiniteRk) {B : Set E} :
    (M.tr t).base B ↔ M.indep B ∧ B.Finite ∧ B.ncard = t :=
  by
  simp_rw [base_iff_maximal_indep, tr.indep_iff', and_imp]
  refine' ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2.antisymm (le_of_not_lt fun hlt => _)⟩, _⟩
  · obtain ⟨B', hB', hBB'⟩ := h.1.1.exists_base_supset
    have : ∃ I, B ⊆ I ∧ I ⊆ B' ∧ I.ncard = t :=
      by
      obtain hfin | hinf := M.finite_or_infinite_rk
      · haveI := hfin
        rw [iff_false_intro M.not_infinite_rk, or_false_iff] at h_rk
        exact exists_intermediate_set' hlt.le (h_rk.trans_eq hB'.card.symm) hBB'
      haveI := hinf
      exact hB'.infinite.exists_supset_ncard_eq hBB' h.1.2.1 hlt.le
    obtain ⟨I, hBI, hIB', rfl⟩ := this
    have hIfin : I.finite := finite_of_ncard_pos ((Nat.zero_le _).trans_lt hlt)
    have := h.2 I (hB'.indep.subset hIB') hIfin rfl.le hBI
    subst this
    exact hlt.ne rfl
  rintro ⟨hB, hBfin, rfl⟩
  exact ⟨⟨hB, hBfin, rfl.le⟩, fun I hI hIfin hIB hBI => eq_of_subset_of_ncard_le hBI hIB hIfin⟩

theorem tr.base_iff [FiniteRk M] (h_rk : t ≤ M.rk) {B : Set E} :
    (M.tr t).base B ↔ M.indep B ∧ B.ncard = t :=
  by
  rw [tr.base_iff' (Or.inl h_rk)]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.Finite, h.2⟩⟩

@[simp]
theorem tr_zero_eq_loopy (M : Matroid E) : M.tr 0 = loopyOn E :=
  by
  refine' eq_of_indep_iff_indep_forall fun I => _
  rw [loopy_on.indep_iff_empty, tr.indep_iff', le_zero_iff]
  exact
    ⟨fun h => (ncard_eq_zero h.2.1).mp h.2.2, by
      rintro rfl
      simp⟩

theorem tr.cl_eq_univ_of_le_r {X : Set E} (h : t ≤ M.R X) : (M.tr t).cl X = univ :=
  by
  have h_rk : t ≤ M.rk ∨ M.infinite_rk :=
    by
    refine' M.finite_or_infinite_rk.elim _ Or.inr
    intro
    exact Or.inl (h.trans (M.r_le_rk _))
  simp_rw [← base_subset_iff_cl_eq_univ, tr.base_iff' h_rk]
  obtain ⟨J, hJ⟩ := M.exists_basis X
  obtain hf | hi := J.finite_or_infinite
  · obtain ⟨I, hIJ, rfl⟩ := exists_smaller_set J t (by rwa [hJ.card])
    exact ⟨I, hIJ.trans hJ.subset, hJ.indep.subset hIJ, hf.subset hIJ, rfl⟩
  obtain ⟨I, hIJ, hIfin, rfl⟩ := hi.exists_subset_ncard_eq t
  exact ⟨I, hIJ.trans hJ.subset, hJ.indep.subset hIJ, hIfin, rfl⟩

theorem Basis.tr_basis_of_r_le [FiniteRk M] (hI : M.Basis I X) (hX : M.R X ≤ t) :
    (M.tr t).Basis I X :=
  Indep.basis_of_forall_insert (tr.indep_iff.mpr ⟨hI.indep, by rwa [hI.card]⟩) hI.Subset
    fun e he hi => he.2 (hI.mem_of_insert_indep he.1 (tr.indep_iff.mp hi).1)

theorem tr.cl_eq_cl_of_r_lt [FiniteRk M] (h : M.R X < t) : (M.tr t).cl X = M.cl X :=
  by
  obtain ⟨J, hJ⟩ := M.exists_basis X
  have hJ' := hJ.tr_basis_of_r_le h.le
  rw [← hJ'.cl, ← hJ.cl]
  ext e
  refine'
    (em (e ∈ J)).elim (fun heJ => iff_of_true (mem_cl_of_mem _ heJ) (mem_cl_of_mem _ heJ))
      fun heJ => _
  rw [hJ.indep.mem_cl_iff_of_not_mem heJ, hJ'.indep.mem_cl_iff_of_not_mem heJ, not_iff_not,
    tr.indep_iff, and_iff_left_iff_imp, ncard_insert_of_not_mem heJ hJ.finite, Nat.add_one_le_iff,
    hJ.card]
  exact fun _ => h

/-- This doesn't need `finite_rk M` to be true, but it's a bit of a pain to prove all the previous
stuff at the right generality. TODO. -/
theorem tr.isQuotient (M : Matroid E) [FiniteRk M] (t : ℕ) : M.tr t ≼ M := fun X =>
  (lt_or_le (M.R X) t).elim (fun h => (tr.cl_eq_cl_of_r_lt h).symm.Subset) fun h =>
    (subset_univ _).trans_eq (tr.cl_eq_univ_of_le_r h).symm

end Truncation

section Uniform

variable {E : Type _} {s t r : ℕ} {I B X : Set E} {M : Matroid E}

/-- The matroid whose bases are the `r`-sets. If `E` is smaller than `r`, then this is the free
  matroid. -/
def unifOn (E : Type _) (r : ℕ) : Matroid E :=
  tr (freeOn E) r

instance {E : Type _} {r : ℕ} : FiniteRk (unifOn E r) :=
  by
  obtain ⟨B, hB⟩ := (unif_on E r).exists_base
  refine' hB.finite_rk_of_finite _
  have hi := hB.indep
  rw [unif_on, tr.indep_iff'] at hi
  exact hi.2.1

/-- the rank-`a` uniform matroid on `b` elements with ground set `fin b`. Free if `b ≤ a`. -/
@[reducible]
def unif (a b : ℕ) : Matroid (Fin b) :=
  unifOn (Fin b) a

theorem unifOn_eq_tr (E : Type _) (r : ℕ) : unifOn E r = tr (freeOn E) r :=
  rfl

@[simp]
theorem unifOn_r [Finite E] (X : Set E) : (unifOn E r).R X = min r X.ncard :=
  by
  rw [unif_on, tr.r_eq _ r, free_on.r_eq]
  infer_instance

theorem unifOn_rk [Finite E] (hr : r ≤ Nat.card E) : (unifOn E r).rk = r :=
  by
  rw [rk, unif_on_r univ, ncard_univ, min_eq_left hr]
  infer_instance

theorem unif.indep_iff' : (unifOn E r).indep I ↔ I.Finite ∧ I.ncard ≤ r := by
  rw [unif_on, tr.indep_iff', iff_true_intro (free_on.indep _), true_and_iff]

@[simp]
theorem unif.indep_iff [Finite E] {I : Set E} : (unifOn E r).indep I ↔ I.ncard ≤ r := by
  rw [indep_iff_r_eq_card, unif_on_r, min_eq_right_iff]

theorem unifOn_free_iff_card_le_r [Finite E] : Nat.card E ≤ r ↔ unifOn E r = freeOn E := by
  rw [← univ_indep_iff_eq_free_on, unif.indep_iff, ncard_univ]

@[simp]
theorem unifOn_zero_eq_loopy (E : Type _) : unifOn E 0 = loopyOn E := by
  rw [unif_on, tr_zero_eq_loopy]

theorem unifOn_base_iff [Finite E] (hr : r ≤ Nat.card E) : (unifOn E r).base B ↔ B.ncard = r :=
  by
  rw [unif_on_eq_tr, tr.base_iff, iff_true_intro (free_on.indep _), true_and_iff]
  rwa [free_on.rk_eq]

@[simp]
theorem unifOn_circuit_iff {C : Set E} : (unifOn E r).Circuit C ↔ C.ncard = r + 1 :=
  by
  obtain rfl | ⟨e, heC⟩ := C.eq_empty_or_nonempty
  ·
    exact
      iff_of_false (empty_not_circuit _)
        (by
          rw [ncard_empty]
          apply NeZero.ne')
  obtain hinf | hfin := C.finite_or_infinite.symm
  ·
    refine'
      iff_of_false (fun hC => hinf hC.Finite)
        (by
          rw [hinf.ncard]
          apply NeZero.ne')
  simp_rw [circuit_iff_dep_forall_diff_singleton_indep, unif.indep_iff', not_and, not_le,
    Nat.lt_iff_add_one_le, iff_true_intro hfin, true_imp_iff]
  refine' ⟨fun h => h.1.antisymm' _, fun h => ⟨h.symm.le, fun f hf => ⟨hfin.diff _, _⟩⟩⟩
  · rw [← ncard_diff_singleton_add_one heC hfin, add_le_add_iff_right]
    exact (h.2 e heC).2
  rw [ncard_diff_singleton_of_mem hf hfin, h, add_tsub_cancel_right]

@[simp]
theorem unifOn_flat_iff [Finite E] {F : Set E} : (unifOn E r).Flat F ↔ F = univ ∨ F.ncard < r :=
  by
  simp_rw [flat_iff_forall_circuit, unif_on_circuit_iff]
  refine' ⟨fun h => (lt_or_le F.ncard r).elim Or.inr fun hle => Or.inl _, _⟩
  · obtain ⟨X, hXF, rfl⟩ := exists_smaller_set F r hle
    refine' eq_univ_of_forall fun x => (em (x ∈ X)).elim (fun h' => hXF h') fun hxF => _
    refine' h (insert x X) x (by rw [ncard_insert_of_not_mem hxF]) (mem_insert _ _) _
    exact insert_subset_insert hXF
  rintro (rfl | hlt)
  · exact fun _ _ _ _ _ => mem_univ _
  refine' fun C e hcard heC hCF => by_contra fun heF' => _
  rw [Nat.lt_iff_add_one_le] at hlt
  have hle := ncard_le_of_subset hCF
  rw [hcard, ncard_insert_of_not_mem heF'] at hle
  linarith

theorem unifOn_dual (E : Type _) [Finite E] {r₁ r₂ : ℕ} (h : r₁ + r₂ = Nat.card E) :
    unifOn E r₁﹡ = unifOn E r₂ := by
  ext X
  rw [unif_on_base_iff (le_of_add_le_right h.le), dual.base_iff,
    unif_on_base_iff (le_of_add_le_left h.le)]
  zify  at *;
  constructor <;>
    · intro h
      linarith [ncard_add_ncard_compl X]

/-- This uses `nat` subtraction, but could be a `simp` lemma, unlike the previous one. -/
theorem unifOn_dual' (E : Type _) [Finite E] {r : ℕ} : unifOn E r﹡ = unifOn E (Nat.card E - r) :=
  by
  obtain hr | hr := le_or_lt r (Nat.card E)
  · rw [unif_on_dual _ (add_tsub_cancel_of_le hr)]
  rw [unif_on_free_iff_card_le_r.mp hr.le, tsub_eq_zero_of_le hr.le, unif_on_zero_eq_loopy,
    free_on.dual]

@[simp]
theorem unifOn_loopless (E : Type _) (ht : t ≠ 0) : (unifOn E t).Loopless := by
  simp_rw [loopless, unif_on, tr.nonloop_iff ht, free_on.nonloop, imp_true_iff]

theorem unifOn_loopless_iff (E : Type _) [Nonempty E] : (unifOn E r).Loopless ↔ r ≠ 0 :=
  by
  refine' ⟨_, unif_on_loopless E⟩
  rintro h rfl
  rw [unif_on_zero_eq_loopy] at h
  exact h (Classical.arbitrary _) (loopy_on.loop _)

theorem unifOn_simple_iff (E : Type _) (hE : 1 < Nat.card E) {r : ℕ} :
    (unifOn E r).simple ↔ 1 < r :=
  by
  have : Finite E := by
    rw [← finite_univ_iff]
    refine' finite_of_ncard_pos _
    rw [ncard_univ]
    linarith
  rw [← ncard_univ, one_lt_ncard_iff] at hE
  obtain ⟨a, b, -, -, hab⟩ := hE
  simp_rw [simple, unif.indep_iff]
  obtain hle | hlt := le_or_lt r 1
  · refine' iff_of_false _ hle.not_lt
    push_neg
    refine'
      ⟨a, b,
        hle.trans_lt
          (by
            rw [ncard_eq_two.mpr ⟨a, b, hab, rfl⟩]
            exact one_lt_two)⟩
  refine' iff_of_true (fun e f => le_trans _ hlt) hlt
  rw [← union_singleton]
  exact (ncard_union_le _ _).trans (by simp)

end Uniform

end Matroid

