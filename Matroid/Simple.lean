import Matroid.Rank
import Project.Mathlib.FinsumNcard

noncomputable section

open Classical

open BigOperators

open Set

namespace Matroid

variable {E E' : Type _} {N M : Matroid E} {e f g : E} {X Y Z S T : Set E}

section Simple

/-- A matroid is loopless on a set if that set doesn't contain a loop. -/
def LooplessOn (M : Matroid E) (X : Set E) : Prop :=
  ∀ ⦃e⦄, e ∈ X → M.Nonloop e

/-- A matroid is loopless if it has no loop -/
def Loopless (M : Matroid E) : Prop :=
  ∀ e, M.Nonloop e

protected theorem Loopless.looplessOn (hM : M.Loopless) : M.LooplessOn X := fun e _ => hM _

@[simp]
theorem looplessOn_univ : M.LooplessOn univ ↔ M.Loopless := by simp [loopless_on, loopless]

theorem LooplessOn.subset (h : M.LooplessOn Y) (hXY : X ⊆ Y) : M.LooplessOn X :=
  subset_trans hXY h

theorem LooplessOn.indep_of_mem (h : M.LooplessOn X) (he : e ∈ X) : M.indep {e} :=
  indep_singleton.2 <| h he

def Loopless.nonloop (hM : M.Loopless) (e : E) : M.Nonloop e :=
  hM e

theorem Loopless.loops (hM : M.Loopless) : M.cl ∅ = ∅ :=
  eq_empty_iff_forall_not_mem.mpr hM

theorem loopless_iff_loops_eq_empty : M.Loopless ↔ M.cl ∅ = ∅ :=
  ⟨Loopless.loops, fun h e he => not_mem_empty e (by rwa [← h])⟩

/-- the property of a set containing no loops or para pairs -/
def SimpleOn (M : Matroid E) (X : Set E) : Prop :=
  ∀ ⦃e⦄, e ∈ X → ∀ ⦃f⦄, f ∈ X → M.indep {e, f}

/-- the property of a matroid having no loops or para pairs -/
def Simple (M : Matroid E) : Prop :=
  ∀ e f, M.indep {e, f}

protected theorem Simple.simpleOn (hM : M.simple) (X : Set E) : M.SimpleOn X := fun e _ f _ =>
  hM e f

@[simp]
theorem simpleOn_univ : M.SimpleOn univ ↔ M.simple := by simp [simple_on, simple]

theorem SimpleOn.subset (h : M.SimpleOn Y) (hXY : X ⊆ Y) : M.SimpleOn X := fun e he f hf =>
  h (hXY he) (hXY hf)

protected theorem SimpleOn.looplessOn (h : M.SimpleOn X) : M.LooplessOn X :=
  by
  intro x hx
  rw [← indep_singleton, ← pair_eq_singleton]
  exact h hx hx

protected theorem Simple.loopless (h : M.simple) : M.Loopless :=
  looplessOn_univ.1 (h.SimpleOn _).LooplessOn

theorem Simple.nonloop (h : M.simple) (e : E) : M.Nonloop e :=
  h.Loopless e

theorem SimpleOn.indep_of_card_le_two_of_finite (h : M.SimpleOn X) (hX : X.ncard ≤ 2)
    (hXfin : X.Finite) : M.indep X :=
  by
  obtain h2 | hlt2 := eq_or_lt_of_le hX
  · obtain ⟨x, y, -, rfl⟩ := ncard_eq_two.mp h2
    exact h (mem_insert _ _) (mem_insert_of_mem _ <| mem_singleton _)
  obtain h1 | hlt1 := eq_or_lt_of_le (nat.lt_succ_iff.mp hlt2)
  · obtain ⟨a, rfl⟩ := ncard_eq_one.mp h1
    rw [indep_singleton]
    exact h.loopless_on (mem_singleton _)
  convert M.empty_indep
  rwa [Nat.lt_add_one_iff, le_zero_iff, ncard_eq_zero hXfin] at hlt1

theorem SimpleOn.indep_of_card_le_two [Finite E] (h : M.SimpleOn X) (hX : X.ncard ≤ 2) :
    M.indep X :=
  h.indep_of_card_le_two_of_finite hX (toFinite _)

theorem SimpleOn.eq_of_r_pair_eq_one (h : M.SimpleOn X) (he : e ∈ X) (hf : f ∈ X)
    (hef : M.R {e, f} = 1) : e = f := by
  rw [(h he hf).R] at hef
  exact ncard_le_one_iff.mp hef.le (by simp) (by simp)

theorem loopless_iff_forall_circuit : M.Loopless ↔ ∀ C, M.Circuit C → C.Finite → 1 < C.ncard :=
  by
  refine' ⟨fun hM C hC hCfin => lt_of_not_le fun hle => _, fun h e he => _⟩
  · obtain rfl | ⟨a, rfl⟩ := (ncard_le_one_iff_eq hCfin).mp hle
    · simpa using hC.nonempty
    exact hM a (loop_iff_circuit.mpr hC)
  exact (h _ he.circuit (finite_singleton e)).Ne (ncard_singleton e).symm

theorem loopless_iff_girth_ne_one : M.Loopless ↔ M.girth ≠ 1 :=
  by
  obtain h0 | hpos := Nat.eq_zero_or_pos M.girth
  · rw [iff_true_intro (ne_of_eq_of_ne h0 Nat.zero_ne_one), iff_true_iff,
      loopless_iff_forall_circuit]
    rw [girth_eq_zero_iff] at h0
    exact fun C hC hCfin => (h0 C hC hCfin).elim
  have hpos' := hpos
  rw [← Nat.succ_le_iff, ← ne_iff_lt_iff_le, ne_comm] at hpos
  simp_rw [hpos, ← Nat.succ_le_iff, le_girth_iff hpos'.ne.symm, Nat.succ_le_iff,
    loopless_iff_forall_circuit]

theorem simple_iff_forall_circuit : M.simple ↔ ∀ C, M.Circuit C → C.Finite → 2 < C.ncard :=
  by
  refine' ⟨fun h C hC hCfin => lt_of_not_le fun hle => hC.dep _, fun h e f => by_contra fun hd => _⟩
  · exact (h.simple_on C).indep_of_card_le_two_of_finite hle hCfin
  obtain ⟨C, hCef, hC⟩ := dep_iff_supset_circuit.mp hd
  have con := (h C hC ((to_finite _).Subset hCef)).trans_le (ncard_le_of_subset hCef)
  have con' := con.trans_le (ncard_insert_le _ _)
  simpa [ncard_singleton] using con'

theorem simple_iff_girth : M.simple ↔ M.girth = 0 ∨ 2 < M.girth :=
  by
  obtain h0 | hpos := Nat.eq_zero_or_pos M.girth
  · rw [iff_true_intro h0, true_or_iff, iff_true_iff, simple_iff_forall_circuit]
    rw [girth_eq_zero_iff] at h0
    exact fun C hC hCfin => (h0 C hC hCfin).elim
  simp_rw [← Nat.succ_le_iff, iff_false_intro hpos.ne.symm, false_or_iff, le_girth_iff hpos.ne.symm,
    Nat.succ_le_iff, simple_iff_forall_circuit]

end Simple

section Parallel

/-- Two nonloops are parallel if they have the same closure -/
def Para (M : Matroid E) (e f : E) : Prop :=
  M.Nonloop e ∧ M.cl {e} = M.cl {f}

theorem Para.cl_eq_cl (h : M.Para e f) : M.cl {e} = M.cl {f} :=
  h.2

theorem Para.nonloop_left (h : M.Para e f) : M.Nonloop e :=
  h.1

theorem Para.nonloop_right (h : M.Para e f) : M.Nonloop f :=
  h.nonloop_left.nonloop_of_mem_cl (h.cl_eq_cl.Subset (mem_cl_self _ _))

theorem Nonloop.para_self (he : M.Nonloop e) : M.Para e e :=
  ⟨he, rfl⟩

theorem Nonloop.nonloop_para_iff_mem_cl (he : M.Nonloop e) (hf : M.Nonloop f) :
    M.Para e f ↔ f ∈ M.cl {e} :=
  ⟨fun h => h.cl_eq_cl.symm.Subset (mem_cl_self _ _), fun h => ⟨he, (hf.cl_eq_of_mem_cl h).symm⟩⟩

theorem Nonloop.para_of_nonloop_mem_cl (he : M.Nonloop e) (hf : M.Nonloop f) (h : f ∈ M.cl {e}) :
    M.Para e f :=
  (he.nonloop_para_iff_mem_cl hf).mpr h

theorem Para.symm (h : M.Para e f) : M.Para f e :=
  ⟨h.nonloop_right, h.2.symm⟩

theorem Para.comm : M.Para e f ↔ M.Para f e :=
  ⟨Para.symm, Para.symm⟩

theorem Para.trans (hef : M.Para e f) (hfg : M.Para f g) : M.Para e g :=
  ⟨hef.1, hef.2.trans hfg.2⟩

theorem Loop.not_para (he : M.Loop e) (f : E) : ¬M.Para e f := fun h => h.nonloop_left he

theorem para_self_iff_nonloop : M.Para e e ↔ M.Nonloop e :=
  ⟨Para.nonloop_left, Nonloop.para_self⟩

theorem Para.indep_iff_eq (hef : M.Para e f) : M.indep {e, f} ↔ e = f :=
  by
  refine' ⟨fun h => by_contra fun hne => _, fun h => _⟩
  · have h' := hef.nonloop_left.indep.mem_cl_iff_of_not_mem (Ne.symm hne)
    rw [iff_not_comm, pair_comm] at h'
    rw [h', hef.cl_eq_cl] at h
    exact h (mem_cl_self _ _)
  subst h
  rw [pair_eq_singleton]
  exact hef.nonloop_left.indep

theorem Nonloop.para_iff_dep_of_ne (he : M.Nonloop e) (hf : M.Nonloop f) (hef : e ≠ f) :
    M.Para e f ↔ ¬M.indep {e, f} :=
  by
  refine' ⟨fun h h' => hef (h.indep_iff_eq.mp h'), fun h => he.para_of_nonloop_mem_cl hf _⟩
  rw [he.indep.mem_cl_iff, pair_comm]
  exact False.elim ∘ h

theorem Simple.eq_of_para (h : M.simple) (hef : M.Para e f) : e = f :=
  hef.indep_iff_eq.mp (h e f)

theorem Simple.para_iff_eq (h : M.simple) : M.Para e f ↔ e = f :=
  ⟨h.eq_of_para, by
    rintro rfl
    exact (h.nonloop e).para_self⟩

theorem simple_iff_para_iff_eq_forall : M.simple ↔ ∀ e f, M.Para e f ↔ e = f :=
  by
  refine' ⟨fun h e f => h.para_iff_eq, fun h e f => _⟩
  have he : M.nonloop e := fun hl => mt (h e e).mpr (hl.not_para _) rfl
  have hf : M.nonloop f := fun hl => mt (h f f).mpr (hl.not_para _) rfl
  obtain rfl | hef := eq_or_ne e f
  · rwa [pair_eq_singleton, indep_singleton]
  exact not_not.mp (by rwa [← he.para_iff_dep_of_ne hf hef, h])

/-- Being parallel is a partial equivalence relation (irreflexive on precisely the loops) -/
instance (M : Matroid E) : IsPer E M.Para
    where
  symm _ _ := Para.symm
  trans _ _ _ := Para.trans

/-- The set of elements parallel to `e` -/
def pcl (M : Matroid E) (e : E) :=
  { f | M.Para e f }

@[simp]
theorem mem_pcl_iff : e ∈ M.pcl f ↔ M.Para e f :=
  Para.comm

theorem Nonloop.mem_pcl_self (he : M.Nonloop e) : e ∈ M.pcl e :=
  he.para_self

theorem Loop.pcl_eq_empty (he : M.Loop e) : M.pcl e = ∅ :=
  eq_empty_of_forall_not_mem fun f => he.not_para _

theorem Loop.not_mem_pcl (he : M.Loop e) (f : E) : e ∉ M.pcl f := fun hef =>
  he.not_para _ (mem_pcl_iff.mpr hef)

theorem pcl_eq_cl_diff_loops (M : Matroid E) (e : E) : M.pcl e = M.cl {e} \ M.cl ∅ :=
  by
  refine'
    (M.loop_or_nonloop e).elim (fun he => by rw [he.pcl_eq_empty, he.cl, diff_self]) fun he => _
  refine' Set.ext fun f => (M.loop_or_nonloop f).elim (fun hf => _) fun hf => _
  · rw [mem_pcl_iff, ← hf.cl]
    exact iff_of_false (hf.not_para _) fun h => h.2 (mem_cl_self _ _)
  rw [pcl, mem_set_of, he.nonloop_para_iff_mem_cl hf, mem_diff, ← loop_iff_mem_cl_empty,
    not_loop_iff, iff_true_intro hf, and_true_iff]

theorem Loopless.pcl_eq_cl (h : M.Loopless) (e : E) : M.pcl e = M.cl {e} := by
  rw [pcl_eq_cl_diff_loops, h.loops, diff_empty]

theorem Nonloop.point_of_pcl_union_loops (he : M.Nonloop e) : M.Point (M.pcl e ∪ M.cl ∅) :=
  by
  rw [pcl_eq_cl_diff_loops, diff_union_self,
    union_eq_self_of_subset_right (M.cl_subset (empty_subset _))]
  exact he.cl_point

theorem Loopless.point_of_pcl (h : M.Loopless) (e : E) : M.Point (M.pcl e) :=
  by
  convert(h.nonloop e).point_of_pcl_union_loops
  rw [h.loops, union_empty]

theorem Para.pcl_eq_pcl (h : M.Para e f) : M.pcl e = M.pcl f :=
  by
  simp_rw [Set.ext_iff, mem_pcl_iff]
  exact fun x => ⟨fun hxe => hxe.trans h, fun hxf => hxf.trans h.symm⟩

theorem Nonloop.para_iff_pcl_eq_pcl (he : M.Nonloop e) : M.Para e f ↔ M.pcl e = M.pcl f :=
  ⟨Para.pcl_eq_pcl, fun h => Para.symm (h.Subset he.mem_pcl_self)⟩

theorem Simple.pcl_eq_singleton (h : M.simple) (e : E) : M.pcl e = {e} :=
  eq_singleton_iff_unique_mem.mpr
    ⟨(h.Nonloop e).mem_pcl_self, fun f hf => h.eq_of_para (mem_pcl_iff.mpr hf)⟩

theorem Simple.cl_eq_singleton (h : M.simple) (e : E) : M.cl {e} = {e} := by
  rw [← h.pcl_eq_singleton, pcl_eq_cl_diff_loops, h.loopless.loops, diff_empty, cl_cl]

theorem simple_iff_forall_pcl_eq_self : M.simple ↔ ∀ e, M.pcl e = {e} :=
  by
  refine' ⟨simple.pcl_eq_singleton, fun h => simple_iff_para_iff_eq_forall.mpr fun e f => _⟩
  rw [nonloop.para_iff_pcl_eq_pcl, h, h, singleton_eq_singleton_iff]
  refine' fun hl => _
  have h' := hl.pcl_eq_empty
  rw [h e] at h'
  exact singleton_ne_empty _ h'

theorem Simple.singleton_point (hM : M.simple) (e : E) : M.Point {e} :=
  by
  convert hM.loopless.point_of_pcl e
  rw [hM.pcl_eq_singleton]

/-- In a `simple` matroid, points are (noncomputably) equivalent to elements. -/
noncomputable def Simple.elemPointEquiv (h : M.simple) : E ≃ { P // M.Point P }
    where
  toFun e :=
    ⟨{e}, by
      rw [← h.cl_eq_singleton]
      exact (h.nonloop e).cl_point⟩
  invFun P := P.2.Nonempty.some
  left_inv e := mem_singleton_iff.mp (Nonempty.some_mem _)
  right_inv := by
    rintro ⟨P, hP⟩
    obtain ⟨e, he, rfl⟩ := hP.exists_eq_cl_nonloop
    simp only [h.loopless.pcl_eq_cl]
    simp_rw [h.cl_eq_singleton, singleton_eq_singleton_iff, ← mem_singleton_iff]
    exact nonempty.some_mem _

@[simp]
theorem Simple.elemPointEquiv_apply_coe (h : M.simple) (e : E) :
    (h.elemPointEquiv e : Set E) = {e} :=
  rfl

@[simp]
theorem Simple.elemPointEquiv_apply_symm (h : M.simple) (P : { P // M.Point P }) :
    {h.elemPointEquiv.symm P} = (P : Set E) :=
  by
  obtain ⟨P, hP⟩ := P
  obtain ⟨e, he, rfl⟩ := hP.exists_eq_cl_nonloop
  simp_rw [h.cl_eq_singleton, simple.elem_point_equiv, Subtype.val_eq_coe, Subtype.coe_mk,
    Equiv.coe_fn_symm_mk, singleton_eq_singleton_iff, ← mem_singleton_iff]
  apply nonempty.some_mem

theorem Simple.elemPointEquiv_apply_symm_mem (h : M.simple) (P : { P // M.Point P }) :
    h.elemPointEquiv.symm P ∈ (P : Set E) := by simp [← singleton_subset_iff]

theorem pcl_pairwiseDisjoint (M : Matroid E) : PairwiseDisjoint (range M.pcl) id :=
  by
  rw [pairwise_disjoint, Set.Pairwise]
  simp only [mem_range, Ne.def, Function.onFun_apply, id.def, forall_exists_index,
    forall_apply_eq_imp_iff', disjoint_iff_forall_ne, mem_pcl_iff]
  rintro e f hef x hex _ hey rfl
  rw [← hex.nonloop_right.para_iff_pcl_eq_pcl] at hef
  exact hef (hex.symm.trans hey)

theorem sum_ncard_point_diff_loops [Finite E] (M : Matroid E) :
    (∑ᶠ P : { P // M.Point P }, ((P : Set E) \ M.cl ∅).ncard) = M.cl ∅ᶜ.ncard :=
  by
  convert@finsum_subtype_eq_finsum_cond _ _ _ (fun P => (P \ M.cl ∅).ncard) M.point
  convert@ncard_eq_finsum_fiber _ _ (M.cl ∅ᶜ) (to_finite _) fun e => M.cl {e}
  ext P
  rw [finsum_eq_if]
  split_ifs
  · congr
    ext e
    simp_rw [mem_diff, mem_inter_iff, mem_compl_iff, mem_preimage, mem_singleton_iff, and_comm',
      and_congr_left_iff]
    intro he
    rw [h.eq_cl_singleton_iff, nonloop_iff_not_mem_cl_empty, and_iff_left he]
  rw [eq_comm, ncard_eq_zero, ← disjoint_iff_inter_eq_empty, disjoint_compl_left_iff_subset]
  rintro e (rfl : M.cl {e} = P)
  rw [← loop, ← not_nonloop_iff]
  exact mt nonloop.cl_point h

theorem Loopless.sum_ncard_point [Finite E] (h : M.Loopless) :
    (∑ᶠ P : { P // M.Point P }, (P : Set E).ncard) = (univ : Set E).ncard :=
  by
  rw [← @diff_empty _ univ, ← h.loops, ← compl_eq_univ_diff, ← sum_ncard_point_diff_loops]
  apply finsum_congr fun P => _
  rw [h.loops, diff_empty]

end Parallel

section PointCount

def numPoints (M : Matroid E) :=
  Nat.card { P // M.Point P }

theorem simple_iff_numPoints_eq_card [Finite E] (hnl : ¬M.base ∅) :
    M.simple ↔ M.numPoints = ncard (univ : Set E) :=
  by
  rw [num_points]
  refine' ⟨fun h => _, fun h => _⟩
  · rw [ncard_univ]
    exact Nat.card_eq_of_bijective _ h.elem_point_equiv.symm.bijective
  simp_rw [simple_iff_forall_pcl_eq_self, pcl_eq_cl_diff_loops]
  rw [← finsum_one, ← union_compl_self (M.cl ∅), ncard_union_eq, ← sum_ncard_point_diff_loops] at h
  swap
  exact disjoint_compl_right
  have hleP : ∀ P : { P // M.point P }, 1 ≤ ((P : Set E) \ M.cl ∅).ncard :=
    by
    rintro ⟨P, hP⟩
    rw [Nat.succ_le_iff, ncard_pos, Subtype.coe_mk]
    exact hP.diff_loops_nonempty
  have hnll : M.loopless :=
    by
    rw [loopless_iff_loops_eq_empty, ← ncard_eq_zero]
    linarith [@finsum_le_finsum { P // M.point P } ℕ _ (fun P => 1)
        (fun P => ((P : Set E) \ M.cl ∅).ncard) (to_finite _) (to_finite _) hleP]
  simp_rw [loopless_iff_loops_eq_empty.mp hnll, diff_empty] at hleP h⊢
  rw [ncard_empty, zero_add] at h
  have hsq := eq_of_finsum_ge_finsum_of_forall_le (to_finite _) (to_finite _) hleP h.symm.le
  simp only [Subtype.forall, Subtype.coe_mk, @eq_comm _ 1, ncard_eq_one] at hsq
  intro e
  obtain ⟨f, hf⟩ := hsq _ (hnll e).cl_point
  have hef : e = f := (hf.subset (M.mem_cl_self e) : e = f)
  rwa [hef] at hf⊢

end PointCount

end Matroid

