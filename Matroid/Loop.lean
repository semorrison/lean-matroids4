import Matroid.Flat

/-
  A `loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.cl ∅`.
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of
  `{e | M.loop e}` or similar. A `nonloop` is simply an element that is not a loop, but we give
  it a definition for the sake of dot notation.
-/
/-
  A `loop` of a matroid is a one-element circuit, or, definitionally, a member of `M.cl ∅`.
  Thus, the set of loops of `M` is equal to `M.cl ∅`, and we prefer this notation instead of
  `{e | M.loop e}` or similar. A `nonloop` is simply an element that is not a loop, but we give
  it a definition for the sake of dot notation.
-/
open Classical

variable {E : Type _} {M M₁ M₂ : Matroid E} {I C X Y Z K F F₁ F₂ : Set E} {e f x y z : E}

open Set

namespace Matroid

-- ### Loops
/-- A loop is a member of the closure of the empty set -/
def Loop (M : Matroid E) (e : E) : Prop :=
  e ∈ M.cl ∅

theorem loop_iff_mem_cl_empty : M.Loop e ↔ e ∈ M.cl ∅ :=
  Iff.rfl

theorem cl_empty_eq_loops (M : Matroid E) : M.cl ∅ = { e | M.Loop e } :=
  rfl

theorem loop_iff_dep : M.Loop e ↔ ¬M.indep {e} := by
  rw [loop_iff_mem_cl_empty, iff_not_comm, M.empty_indep.not_mem_cl_iff, mem_empty_iff_false,
    not_false_iff, true_and_iff, insert_emptyc_eq]

theorem loop_iff_circuit : M.Loop e ↔ M.Circuit {e} :=
  by
  simp_rw [circuit_iff_forall_ssubset, loop_iff_dep, iff_self_and, ssubset_singleton_iff, forall_eq]
  exact fun _ => M.empty_indep

theorem loop_iff_not_mem_base_forall : M.Loop e ↔ ∀ B, M.base B → e ∉ B := by
  simp_rw [loop_iff_dep, indep_iff_subset_base, not_exists, not_and, singleton_subset_iff]

theorem Loop.circuit (he : M.Loop e) : M.Circuit {e} :=
  loop_iff_circuit.mp he

theorem Loop.dep (he : M.Loop e) : ¬M.indep {e} :=
  loop_iff_dep.mp he

theorem Loop.mem_cl (he : M.Loop e) (X : Set E) : e ∈ M.cl X :=
  M.cl_mono (empty_subset _) he

theorem Loop.mem_flat (he : M.Loop e) {F : Set E} (hF : M.Flat F) : e ∈ F :=
  by
  have := he.mem_cl F
  rwa [hF.cl] at this

theorem Flat.loops_subset (hF : M.Flat F) : M.cl ∅ ⊆ F := fun e he => Loop.mem_flat he hF

theorem Loop.dep_of_mem (he : M.Loop e) (h : e ∈ X) : ¬M.indep X := fun hX =>
  he.Circuit.dep (hX.Subset (singleton_subset_iff.mpr h))

theorem Loop.not_mem_indep (he : M.Loop e) (hI : M.indep I) : e ∉ I := fun h => he.dep_of_mem h hI

theorem Loop.eq_of_circuit_mem (he : M.Loop e) (hC : M.Circuit C) (h : e ∈ C) : C = {e} := by
  rw [he.circuit.eq_of_subset_circuit hC (singleton_subset_iff.mpr h)]

theorem Indep.disjoint_loops (hI : M.indep I) : Disjoint I (M.cl ∅) :=
  by_contra fun h =>
    let ⟨e, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    Loop.not_mem_indep he hI heI

theorem Indep.eq_empty_of_subset_loops (hI : M.indep I) (h : I ⊆ M.cl ∅) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun e he => Loop.not_mem_indep (h he) hI he

theorem cl_eq_loops_of_subset (h : X ⊆ M.cl ∅) : M.cl X = M.cl ∅ :=
  (cl_subset_cl h).antisymm (M.cl_mono (empty_subset _))

theorem Loop.cl (he : M.Loop e) : M.cl {e} = M.cl ∅ :=
  cl_eq_loops_of_subset (singleton_subset_iff.mpr he)

theorem loop_iff_cl_eq_cl_empty : M.Loop e ↔ M.cl {e} = M.cl ∅ :=
  ⟨fun h => by rw [h.cl], fun h => by
    rw [loop_iff_mem_cl_empty, ← h]
    exact M.mem_cl_self e⟩

theorem cl_union_eq_cl_of_subset_loops {Y : Set E} (hY : Y ⊆ M.cl ∅) (X : Set E) :
    M.cl (X ∪ Y) = M.cl X := by
  rw [← cl_union_cl_right_eq_cl_union, cl_eq_loops_of_subset hY, cl_union_cl_right_eq_cl_union,
    union_empty]

theorem cl_diff_eq_cl_of_subset_loops {Y : Set E} (hY : Y ⊆ M.cl ∅) (X : Set E) :
    M.cl (X \ Y) = M.cl X := by
  rw [← cl_union_eq_cl_of_subset_loops hY, diff_union_self, cl_union_eq_cl_of_subset_loops hY]

-- ### Nonloops
/-- A `nonloop` is an element that is not a loop -/
def Nonloop (M : Matroid E) (e : E) : Prop :=
  ¬M.Loop e

def nonloops (M : Matroid E) : Set E :=
  { e | M.Nonloop e }

@[simp]
theorem not_loop_iff : ¬M.Loop e ↔ M.Nonloop e :=
  Iff.rfl

@[simp]
theorem not_nonloop_iff : ¬M.Nonloop e ↔ M.Loop e := by rw [← not_loop_iff, Classical.not_not]

theorem nonloops_eq_compl_cl_empty : M.nonloops = M.cl ∅ᶜ :=
  rfl

@[simp]
theorem compl_nonloops_eq_cl_empty : M.nonloopsᶜ = M.cl ∅ := by
  rw [nonloops_eq_compl_cl_empty, compl_compl]

theorem loop_or_nonloop (M : Matroid E) (e : E) : M.Loop e ∨ M.Nonloop e :=
  em _

@[simp]
theorem indep_singleton : M.indep {e} ↔ M.Nonloop e := by
  rw [nonloop, loop_iff_dep, Classical.not_not]

alias indep_singleton ↔ indep.nonloop nonloop.indep

attribute [protected] indep.nonloop nonloop.indep

theorem Indep.nonloop_of_mem (hI : M.indep I) (h : e ∈ I) : ¬M.Loop e := fun he =>
  (he.not_mem_indep hI) h

theorem Cocircuit.nonloop_of_mem {K : Set E} (hK : M.Cocircuit K) (he : e ∈ K) : M.Nonloop e :=
  fun h => (h.mem_flat hK.compl_hyperplane.Flat) he

theorem Circuit.nonloop_of_mem_of_one_lt_card (hC : M.Circuit C) (h : 1 < C.ncard) (he : e ∈ C) :
    M.Nonloop e :=
  not_loop_iff.mp fun hlp => by simpa [hlp.eq_of_circuit_mem hC he] using h

theorem nonloop_of_not_mem_cl (h : e ∉ M.cl X) : M.Nonloop e :=
  not_loop_iff.mp fun he => h (he.mem_cl X)

theorem nonloop_iff_not_mem_cl_empty : M.Nonloop e ↔ e ∉ M.cl ∅ :=
  Iff.rfl

theorem Nonloop.mem_cl_singleton (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : f ∈ M.cl {e} :=
  by
  refine' (M.loop_or_nonloop f).elim (fun hf => hf.mem_cl _) fun hf => _
  rw [he.indep.mem_cl_iff, mem_singleton_iff]
  rwa [hf.indep.mem_cl_iff, mem_singleton_iff, eq_comm, pair_comm] at hef

theorem Nonloop.mem_cl_comm (he : M.Nonloop e) (hf : M.Nonloop f) : f ∈ M.cl {e} ↔ e ∈ M.cl {f} :=
  ⟨hf.mem_cl_singleton, he.mem_cl_singleton⟩

theorem Nonloop.nonloop_of_mem_cl (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : M.Nonloop f := fun hf =>
  he (by rwa [hf.cl] at hef)

theorem Nonloop.cl_eq_of_mem_cl (he : M.Nonloop e) (hef : e ∈ M.cl {f}) : M.cl {e} = M.cl {f} :=
  by
  ext x
  obtain hx | hx := M.loop_or_nonloop x
  · exact ⟨fun _ => hx.mem_cl _, fun _ => hx.mem_cl _⟩
  refine' ⟨fun h => _, fun h => he.mem_cl_singleton _⟩
  · rw [← singleton_subset_iff, ← cl_subset_cl_iff_subset_cl] at *
    exact h.trans hef
  have hfx := hx.mem_cl_singleton h
  rw [← singleton_subset_iff, ← cl_subset_cl_iff_subset_cl] at *
  exact hef.trans hfx

theorem Nonloop.cl_eq_cl_iff_dep (he : M.Nonloop e) (hf : M.Nonloop f) :
    M.cl {e} = M.cl {f} ↔ e = f ∨ ¬M.indep {e, f} :=
  by
  rw [← imp_iff_or_not]
  refine' ⟨fun hef => _, fun h => he.cl_eq_of_mem_cl (by rwa [hf.indep.mem_cl_iff])⟩
  have hf : f ∈ M.cl {e} := by
    rw [hef]
    exact M.mem_cl_self f
  rw [pair_comm, eq_comm, ← mem_singleton_iff]
  exact he.indep.mem_cl_iff.mp hf

theorem exists_nonloop_of_empty_not_base (h : ¬M.base ∅) : ∃ e, M.Nonloop e :=
  by
  obtain ⟨B, hB⟩ := M.exists_base
  obtain rfl | ⟨e, he⟩ := B.eq_empty_or_nonempty
  · exact (h hB).elim
  exact ⟨e, hB.indep.nonloop_of_mem he⟩

-- ### Coloops
/-- A coloop is a loop of the dual  -/
def Coloop (M : Matroid E) (e : E) : Prop :=
  M﹡.Loop e

theorem coloop_iff_mem_cl_empty : M.Coloop e ↔ e ∈ M﹡.cl ∅ :=
  Iff.rfl

theorem coloops_eq_dual_cl_empty : { e | M.Coloop e } = M﹡.cl ∅ :=
  rfl

theorem Coloop.dual_loop (he : M.Coloop e) : M﹡.Loop e :=
  he

theorem Loop.dual_coloop (he : M.Loop e) : M﹡.Coloop e := by rwa [coloop, dual_dual]

@[simp]
theorem dual_coloop_iff_loop : M﹡.Coloop e ↔ M.Loop e :=
  ⟨fun h => by
    rw [← dual_dual M]
    exact h.dual_loop, Loop.dual_coloop⟩

@[simp]
theorem dual_loop_iff_coloop : M﹡.Loop e ↔ M.Coloop e :=
  ⟨fun h => by
    rw [← dual_dual M]
    exact h.dual_coloop, Coloop.dual_loop⟩

theorem coloop_iff_forall_mem_base : M.Coloop e ↔ ∀ ⦃B⦄, M.base B → e ∈ B :=
  by
  simp_rw [← dual_loop_iff_coloop, loop_iff_not_mem_base_forall, dual.base_iff]
  exact ⟨fun h B hB => not_mem_compl_iff.mp (h _ (by rwa [compl_compl])), fun h B hB => h hB⟩

theorem Coloop.nonloop (h : M.Coloop e) : M.Nonloop e :=
  let ⟨B, hB⟩ := M.exists_base
  hB.indep.nonloop_of_mem ((coloop_iff_forall_mem_base.mp h) hB)

theorem Loop.not_coloop (h : M.Loop e) : ¬M.Coloop e :=
  by
  rw [← dual_loop_iff_coloop]
  rw [← dual_dual M, dual_loop_iff_coloop] at h
  exact h.nonloop

theorem Coloop.not_mem_circuit (he : M.Coloop e) (hC : M.Circuit C) : e ∉ C :=
  by
  intro heC
  rw [coloop_iff_forall_mem_base] at he
  obtain ⟨B, hB, hCB⟩ := (hC.diff_singleton_indep heC).exists_base_supset
  have h := insert_subset.mpr ⟨he hB, hCB⟩
  rw [insert_diff_singleton, insert_eq_of_mem heC] at h
  exact hC.dep (hB.indep.subset h)

theorem Circuit.not_coloop_of_mem (hC : M.Circuit C) (heC : e ∈ C) : ¬M.Coloop e := fun h =>
  h.not_mem_circuit hC heC

theorem coloop_iff_forall_mem_cl_iff_mem : M.Coloop e ↔ ∀ X, e ∈ M.cl X ↔ e ∈ X :=
  by
  rw [coloop_iff_forall_mem_base]
  refine'
    ⟨fun h => fun X => ⟨fun heX => by_contra fun heX' => _, fun h' => M.subset_cl X h'⟩,
      fun h B hB => (h B).mp (hB.cl.symm.subset (mem_univ e))⟩
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_supset
  exact (hI.mem_cl_iff_of_not_mem heX').mp heX (hB.indep.subset (insert_subset.mpr ⟨h hB, hIB⟩))

theorem Coloop.mem_cl_iff_mem (he : M.Coloop e) : e ∈ M.cl X ↔ e ∈ X :=
  coloop_iff_forall_mem_cl_iff_mem.mp he X

theorem Coloop.mem_of_mem_cl (he : M.Coloop e) (hX : e ∈ M.cl X) : e ∈ X :=
  he.mem_cl_iff_mem.mp hX

@[simp]
theorem cl_inter_coloops_eq (M : Matroid E) (X : Set E) : M.cl X ∩ M﹡.cl ∅ = X ∩ M﹡.cl ∅ :=
  by
  simp_rw [Set.ext_iff, mem_inter_iff, ← coloop_iff_mem_cl_empty, and_congr_left_iff]
  exact fun x => coloop.mem_cl_iff_mem

theorem cl_inter_eq_of_subset_coloops (X : Set E) (hK : K ⊆ M﹡.cl ∅) : M.cl X ∩ K = X ∩ K :=
  by
  refine' inter_eq_inter_iff_right.mpr ⟨(inter_subset_left _ _).trans (M.subset_cl X), _⟩
  refine' ((inter_subset_inter_right (M.cl X) hK).trans (M.cl_inter_coloops_eq X).Subset).trans _
  exact inter_subset_left _ _

theorem cl_union_eq_of_subset_coloops (X : Set E) {K : Set E} (hK : K ⊆ M﹡.cl ∅) :
    M.cl (X ∪ K) = M.cl X ∪ K :=
  by
  rw [← cl_union_cl_left_eq_cl_union]
  refine' (M.subset_cl _).antisymm' fun e he => _
  obtain he' | ⟨C, hC, heC, hCss⟩ := mem_cl_iff_exists_circuit.mp he
  assumption
  have hCX : C \ {e} ⊆ M.cl X :=
    by
    rw [diff_subset_iff, singleton_union]
    exact fun f hfC =>
      (hCss hfC).elim Or.inl fun h' =>
        h'.elim Or.inr fun hfK => (hC.not_coloop_of_mem hfC).elim (hK hfK)
  exact Or.inl (cl_subset_cl hCX (hC.subset_cl_diff_singleton e heC))

theorem cl_eq_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.cl K = K ∪ M.cl ∅ := by
  rw [← empty_union K, cl_union_eq_of_subset_coloops _ hK, empty_union, union_comm]

theorem cl_diff_eq_of_subset_coloops (X : Set E) {K : Set E} (hK : K ⊆ M﹡.cl ∅) :
    M.cl (X \ K) = M.cl X \ K := by
  nth_rw 2 [← inter_union_diff X K]
  rw [union_comm, cl_union_eq_of_subset_coloops _ ((inter_subset_right X K).trans hK),
    union_diff_distrib, diff_eq_empty.mpr (inter_subset_right X K), union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [coloop.mem_cl_iff_mem (hK heK)] at heX
  exact heX.2 heK

theorem cl_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M﹡.cl ∅) :
    Disjoint (M.cl X) K := by
  rwa [disjoint_iff_inter_eq_empty, cl_inter_eq_of_subset_coloops X hK, ←
    disjoint_iff_inter_eq_empty]

theorem cl_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M﹡.cl ∅)) :
    Disjoint (M.cl X) (M﹡.cl ∅) :=
  cl_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

theorem cl_insert_coloop_eq (X : Set E) {he : M.Coloop e} : M.cl (insert e X) = insert e (M.cl X) :=
  by
  rw [← union_singleton, ← union_singleton, cl_union_eq_of_subset_coloops]
  rwa [singleton_subset_iff]

@[simp]
theorem cl_union_coloops_eq (M : Matroid E) (X : Set E) : M.cl (X ∪ M﹡.cl ∅) = M.cl X ∪ M﹡.cl ∅ :=
  cl_union_eq_of_subset_coloops _ Subset.rfl

theorem Coloop.not_mem_cl_of_not_mem (he : M.Coloop e) (hX : e ∉ X) : e ∉ M.cl X :=
  mt he.mem_cl_iff_mem.mp hX

theorem Coloop.insert_indep_of_indep (he : M.Coloop e) (hI : M.indep I) : M.indep (insert e I) :=
  (em (e ∈ I)).elim (fun h => by rwa [insert_eq_of_mem h]) fun h => by
    rwa [hI.insert_indep_iff_of_not_mem h, he.mem_cl_iff_mem]

theorem coloops_indep (M : Matroid E) : M﹡.indep (M.cl ∅) :=
  by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [dual_indep_iff_coindep, coindep_iff_disjoint_base]
  exact ⟨B, hB, hB.indep.disjoint_loops.symm⟩

theorem union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I ∪ K) ↔ M.indep I :=
  ⟨fun h => h.Subset (subset_union_left I K), fun h =>
    indep_iff_forall_subset_not_circuit.mpr fun C hCIK hC =>
      hC.dep
        (h.Subset fun e h' => (hCIK h').elim id fun heK => (hC.not_coloop_of_mem h' (hK heK)).elim)⟩

theorem diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M﹡.cl ∅) : M.indep (I \ K) ↔ M.indep I :=
  by
  rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]

theorem indep_iff_union_coloops_indep : M.indep I ↔ M.indep (I ∪ M﹡.cl ∅) :=
  (union_indep_iff_indep_of_subset_coloops Subset.rfl).symm

theorem indep_iff_diff_coloops_indep : M.indep I ↔ M.indep (I \ M﹡.cl ∅) :=
  (diff_indep_iff_indep_of_subset_coloops Subset.rfl).symm

theorem Coloop.cocircuit (he : M.Coloop e) : M.Cocircuit {e} := by
  rwa [← dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit] at he

theorem coloop_iff_cocircuit : M.Coloop e ↔ M.Cocircuit {e} := by
  rw [← dual_loop_iff_coloop, loop_iff_circuit, dual_circuit_iff_cocircuit]

/-- If two matroids agree on loops and coloops, and have the same independent sets after
  loops/coloops are removed, they are equal. -/
theorem eq_of_indep_iff_indep_forall_disjoint_loops_coloops {M₁ M₂ : Matroid E}
    (hl : M₁.cl ∅ = M₂.cl ∅) (hc : M₁﹡.cl ∅ = M₂﹡.cl ∅)
    (h : ∀ I, Disjoint I (M₁.cl ∅ ∪ M₁﹡.cl ∅) → (M₁.indep I ↔ M₂.indep I)) : M₁ = M₂ :=
  by
  refine' eq_of_indep_iff_indep_forall fun I => _
  rw [indep_iff_diff_coloops_indep, @indep_iff_diff_coloops_indep _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.cl ∅))
  · rw [h]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left (diff_subset _ _) hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.loop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine' iff_of_false (hel.dep_of_mem ⟨heI, hel.not_coloop⟩) _
  rw [loop_iff_mem_cl_empty, hl, ← loop_iff_mem_cl_empty] at hel; rw [hc]
  exact hel.dep_of_mem ⟨heI, hel.not_coloop⟩

end Matroid

