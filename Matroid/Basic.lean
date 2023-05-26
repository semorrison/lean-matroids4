import ForMathlib.Ncard
import ForMathlib.Data.Set.Finite
import Mathlib.Order.Minimal

open Classical

open BigOperators

open Set

variable {E : Type _} {I J B B' B₁ B₂ X Y : Set E} {e f : E}

section Prelim

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def ExchangeProperty (P : Set E → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A predicate `P` on sets satisfies the maximal subset property if, for all `X` containing some
  `I` satisfying `P`, there is a maximal subset of `X` satisfying `P`. -/
def ExistsMaximalSubsetProperty (P : Set E → Prop) : Prop :=
  ∀ I X, P I → I ⊆ X → (maximals (· ⊆ ·) { Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X }).Nonempty

theorem existsMaximalSubsetProperty_of_bounded {P : Set E → Prop}
    (h : ∃ n, ∀ I, P I → I.Finite ∧ I.ncard ≤ n) : ExistsMaximalSubsetProperty P :=
  by
  obtain ⟨n, h⟩ := h
  intro I₀ X hI₀ hI₀X
  set S := { I | P I ∧ I₀ ⊆ I ∧ I ⊆ X } with hS
  have : Nonempty S := ⟨⟨I₀, hI₀, subset.rfl, hI₀X⟩⟩
  set f : { I | P I ∧ I₀ ⊆ I ∧ I ⊆ X } → Fin (n + 1) := fun I =>
    ⟨ncard (I : Set E), Nat.lt_succ_of_le (h I I.2.1).2⟩ with hf
  obtain ⟨m, ⟨⟨J, hJ⟩, rfl⟩, hJmax⟩ := Set.Finite.exists_maximal (range f) (range_nonempty _)
  refine' ⟨J, hJ, fun K hK hJK => (eq_of_subset_of_ncard_le hJK _ (h _ hK.1).1).symm.Subset⟩
  exact (hJmax _ ⟨⟨K, hK⟩, rfl⟩ (ncard_le_of_subset hJK (h _ hK.1).1)).symm.le

private theorem antichain_of_exch {base : Set E → Prop} (exch : ExchangeProperty base) (hB : base B)
    (hB' : base B') (h : B ⊆ B') : B = B' :=
  by
  refine' h.antisymm (diff_eq_empty.mp (eq_empty_iff_forall_not_mem.mpr fun x hx => _))
  obtain ⟨e, he, -⟩ := exch _ _ hB' hB _ hx
  exact he.2 (h he.1)

private theorem diff_aux_of_exch {base : Set E → Prop} (exch : ExchangeProperty base)
    (hB₁ : base B₁) (hB₂ : base B₂) (hfin : (B₁ \ B₂).Finite) :
    (B₂ \ B₁).Finite ∧ (B₂ \ B₁).ncard = (B₁ \ B₂).ncard :=
  by
  suffices :
    ∀ {k B B'},
      base B → base B' → (B \ B').Finite → ncard (B \ B') = k → (B' \ B).Finite ∧ (B' \ B).ncard = k
  exact this hB₁ hB₂ hfin rfl
  intro k
  induction' k with k IH
  · intro B B' hB hB' hfin h0
    rw [ncard_eq_zero hfin, diff_eq_empty] at h0
    rw [antichain_of_exch exch hB hB' h0, diff_self]
    simp
  intro B B' hB hB' hfin hcard
  obtain ⟨e, he⟩ :=
    nonempty_of_ncard_ne_zero
      (by
        rw [hcard]
        simp : (B \ B').ncard ≠ 0)
  obtain ⟨f, hf, hB0⟩ := exch _ _ hB hB' _ he
  have hef : f ≠ e := by
    rintro rfl
    exact hf.2 he.1
  obtain ⟨hfin', hcard'⟩ := IH hB0 hB' _ _
  · rw [insert_diff_singleton_comm hef, diff_diff_right, inter_singleton_eq_empty.mpr he.2,
      union_empty, ← union_singleton, ← diff_diff] at hfin' hcard'
    have hfin'' := hfin'.insert f
    rw [insert_diff_singleton, insert_eq_of_mem hf] at hfin''
    apply_fun fun x => x + 1  at hcard'
    rw [ncard_diff_singleton_add_one hf hfin'', ← Nat.succ_eq_add_one] at hcard'
    exact ⟨hfin'', hcard'⟩
  · rw [insert_diff_of_mem _ hf.1, diff_diff_comm]
    exact hfin.diff _
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ncard_diff_singleton_of_mem he hfin, hcard,
    Nat.succ_sub_one]

private theorem finite_of_finite_of_exch {base : Set E → Prop} (exch : ExchangeProperty base)
    (hB : base B) (hB' : base B') (h : B.Finite) : B'.Finite :=
  by
  rw [← inter_union_diff B' B]
  exact finite.union (h.subset (inter_subset_right _ _)) (diff_aux_of_exch exch hB hB' (h.diff _)).1

private theorem card_eq_card_of_exchange {base : Set E → Prop} (exch : ExchangeProperty base)
    (hB₁ : base B₁) (hB₂ : base B₂) : B₁.ncard = B₂.ncard :=
  by
  obtain hB₁' | hB₁' := B₁.finite_or_infinite.symm
  · rw [hB₁'.ncard, infinite.ncard fun h => hB₁' (finite_of_finite_of_exch exch hB₂ hB₁ h)]
  have hdcard := (diff_aux_of_exch exch hB₁ hB₂ (hB₁'.diff _)).2
  have hB₂' := finite_of_finite_of_exch exch hB₁ hB₂ hB₁'
  rw [← ncard_inter_add_ncard_diff_eq_ncard B₁ B₂ hB₁', ← hdcard, inter_comm,
    ncard_inter_add_ncard_diff_eq_ncard B₂ B₁ hB₂']

end Prelim

/-- A `matroid` is a nonempty collection of sets satisfying the exchange property and the maximal
  subset property. Each such set is called a `base` of the matroid. -/
@[ext]
structure Matroid (E : Type _) where
  base : Set E → Prop
  exists_base' : ∃ B, base B
  base_exchange' : ExchangeProperty base
  maximality : ExistsMaximalSubsetProperty fun I => ∃ B, base B ∧ I ⊆ B

instance {E : Type _} [Finite E] : Finite (Matroid E) :=
  Finite.of_injective (fun M => M.base) fun M₁ M₂ h =>
    by
    ext
    dsimp only at h
    rw [h]

instance {E : Type _} : Nonempty (Matroid E) :=
  ⟨⟨@Eq _ ∅, ⟨_, rfl⟩, by
      rintro _ _ rfl rfl a h
      exfalso
      exact not_mem_empty a h.1,
      existsMaximalSubsetProperty_of_bounded
        ⟨0, by
          rintro I ⟨B, rfl, hIB⟩
          rw [subset_empty_iff.mp hIB]
          simp⟩⟩⟩

namespace Matroid

section Defs

/-- A set is independent if it is contained in a base.  -/
def Indep (M : Matroid E) (I : Set E) : Prop :=
  ∃ B, M.base B ∧ I ⊆ B

/-- A basis for a set `X` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def Basis (M : Matroid E) (I X : Set E) : Prop :=
  I ∈ maximals (· ⊆ ·) { A | M.indep A ∧ A ⊆ X }

/-- A circuit is a minimal dependent set -/
def Circuit (M : Matroid E) (C : Set E) : Prop :=
  C ∈ minimals (· ⊆ ·) { X | ¬M.indep X }

/-- A coindependent set is one that is disjoint from some base -/
def Coindep (M : Matroid E) (I : Set E) : Prop :=
  ∃ B, M.base B ∧ Disjoint I B

class FiniteRk (M : Matroid E) : Prop where
  exists_finite_base : ∃ B, M.base B ∧ B.Finite

class InfiniteRk (M : Matroid E) : Prop where
  exists_infinite_base : ∃ B, M.base B ∧ B.Infinite

class Finitary (M : Matroid E) : Prop where
  cct_finite : ∀ C : Set E, M.Circuit C → C.Finite

class RkPos (M : Matroid E) : Prop where
  empty_not_base : ¬M.base ∅

class DualRkPos (M : Matroid E) : Prop where
  univ_not_base : ¬M.base univ

end Defs

variable {M : Matroid E}

section Base

theorem exists_base (M : Matroid E) : ∃ B, M.base B :=
  M.exists_base'

theorem Base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e})) :=
  M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

theorem Base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {e})) := by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

theorem Base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) : B₁ = B₂ :=
  antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

theorem Base.finite_of_finite (hB : M.base B) (h : B.Finite) (hB' : M.base B') : B'.Finite :=
  finite_of_finite_of_exch M.base_exchange' hB hB' h

theorem Base.infinite_of_infinite (hB : M.base B) (h : B.Infinite) (hB₁ : M.base B₁) :
    B₁.Infinite :=
  by_contra fun hB_inf => (hB₁.finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h

theorem Base.finite [FiniteRk M] (hB : M.base B) : B.Finite :=
  let ⟨B₀, hB₀⟩ := ‹FiniteRk M›.exists_finite_base
  hB₀.1.finite_of_finite hB₀.2 hB

theorem Base.infinite [InfiniteRk M] (hB : M.base B) : B.Infinite :=
  let ⟨B₀, hB₀⟩ := ‹InfiniteRk M›.exists_infinite_base
  hB₀.1.infinite_of_infinite hB₀.2 hB

theorem Base.finiteRk_of_finite (hB : M.base B) (hfin : B.Finite) : FiniteRk M :=
  ⟨⟨B, hB, hfin⟩⟩

theorem Base.infiniteRk_of_infinite (hB : M.base B) (h : B.Infinite) : InfiniteRk M :=
  ⟨⟨B, hB, h⟩⟩

theorem not_finiteRk (M : Matroid E) [InfiniteRk M] : ¬FiniteRk M :=
  by
  intro h
  obtain ⟨B, hB⟩ := M.exists_base
  exact hB.infinite hB.finite

theorem not_infiniteRk (M : Matroid E) [FiniteRk M] : ¬InfiniteRk M :=
  by
  intro h
  obtain ⟨B, hB⟩ := M.exists_base
  exact hB.infinite hB.finite

theorem finite_or_infiniteRk (M : Matroid E) : FiniteRk M ∨ InfiniteRk M :=
  let ⟨B, hB⟩ := M.exists_base
  B.finite_or_infinite.elim (Or.inl ∘ hB.finiteRk_of_finite) (Or.inr ∘ hB.infiniteRk_of_infinite)

instance finiteRk_of_finite [Finite E] {M : Matroid E} : FiniteRk M :=
  let ⟨B, hB⟩ := M.exists_base
  ⟨⟨B, hB, toFinite _⟩⟩

instance finitary_of_finiteRk {M : Matroid E} [FiniteRk M] : Finitary M :=
  ⟨by
    intro C hC
    obtain rfl | ⟨e, heC⟩ := C.eq_empty_or_nonempty
    exact finite_empty
    have hi : M.indep (C \ {e}) := by_contra fun h' => (hC.2 h' (diff_subset _ _) heC).2 rfl
    obtain ⟨B, hB, hCB⟩ := hi
    convert(hB.finite.subset hCB).insert e
    rw [insert_diff_singleton, insert_eq_of_mem heC]⟩

theorem Base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard :=
  card_eq_card_of_exchange M.base_exchange' hB₁ hB₂

theorem Base.diff_finite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite :=
  ⟨fun h => (diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).1, fun h =>
    (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h).1⟩

theorem Base.diff_infinite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite :=
  not_iff_not.mpr (hB₁.diff_finite_comm hB₂)

theorem Base.card_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard :=
  by
  obtain h | h := (B₁ \ B₂).finite_or_infinite
  · rw [(diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).2]
  rw [h.ncard, infinite.ncard fun h' => h (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h').1]

end Base

section Indep

theorem indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B :=
  Iff.rfl

theorem indep_mono {M : Matroid E} {I J : Set E} (hIJ : I ⊆ J) (hJ : M.indep J) : M.indep I :=
  by
  obtain ⟨B, hB, hJB⟩ := hJ
  exact ⟨B, hB, hIJ.trans hJB⟩

theorem Indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B :=
  hI

theorem Indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
  by
  obtain ⟨B, hB, hJB⟩ := hJ
  exact ⟨B, hB, hIJ.trans hJB⟩

@[simp]
theorem empty_indep (M : Matroid E) : M.indep ∅ :=
  Exists.elim M.exists_base fun B hB => ⟨_, hB, B.empty_subset⟩

theorem Indep.finite [FiniteRk M] (hI : M.indep I) : I.Finite :=
  let ⟨B, hB, hIB⟩ := hI
  hB.Finite.Subset hIB

theorem Indep.inter_right (hI : M.indep I) (X : Set E) : M.indep (I ∩ X) :=
  hI.Subset (inter_subset_left _ _)

theorem Indep.inter_left (hI : M.indep I) (X : Set E) : M.indep (X ∩ I) :=
  hI.Subset (inter_subset_right _ _)

theorem Indep.diff (hI : M.indep I) (X : Set E) : M.indep (I \ X) :=
  hI.Subset (diff_subset _ _)

theorem Base.indep (hB : M.base B) : M.indep B :=
  ⟨B, hB, subset_rfl⟩

theorem Base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
  by
  obtain ⟨B', hB', hB'I⟩ := hI
  exact hBI.antisymm (by rwa [hB.eq_of_subset_base hB' (hBI.trans hB'I)])

theorem base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
  by
  refine' ⟨fun h => ⟨h.indep, fun _ => h.eq_of_subset_indep⟩, fun h => _⟩
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h
  rwa [h _ hB'.indep hBB']

theorem base_iff_mem_maximals : M.base B ↔ B ∈ maximals (· ⊆ ·) { I | M.indep I } :=
  by
  rw [base_iff_maximal_indep, maximals]
  exact
    ⟨fun h => ⟨h.1, fun I hI hBI => (h.2 I hI hBI).symm.Subset⟩, fun h =>
      ⟨h.1, fun I hI hBI => hBI.antisymm (h.2 hI hBI)⟩⟩

theorem Indep.base_of_maximal (hI : M.indep I) (h : ∀ J, M.indep J → I ⊆ J → I = J) : M.base I :=
  base_iff_maximal_indep.mpr ⟨hI, h⟩

theorem Base.dep_of_sSubset (hB : M.base B) (h : B ⊂ X) : ¬M.indep X := fun hX =>
  h.Ne (hB.eq_of_subset_indep hX h.Subset)

theorem Base.dep_of_insert (hB : M.base B) (he : e ∉ B) : ¬M.indep (insert e B) :=
  hB.dep_of_sSubset (ssubset_insert he)

theorem Base.exchange_base_of_indep (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.indep (insert f (B \ {e}))) : M.base (insert f (B \ {e})) :=
  by
  obtain ⟨B', hB', hIB'⟩ := hI
  have hBeB' := (subset_insert _ _).trans hIB'
  have heB' : e ∉ B' := by
    intro heB'
    have hBB' : B ⊆ B' :=
      by
      refine' subset_trans _ (insert_subset.mpr ⟨heB', hIB'⟩)
      rw [insert_comm, insert_diff_singleton]
      refine' (subset_insert _ _).trans (subset_insert _ _)
    rw [← hB.eq_of_subset_indep hB'.indep hBB'] at hIB'
    exact hf (hIB' (mem_insert _ _))
  obtain ⟨y, hy, hy'⟩ := hB.exchange hB' ⟨he, heB'⟩
  rw [← hy'.eq_of_subset_base hB' (insert_subset.mpr ⟨hy.1, hBeB'⟩)] at hIB'
  have : f = y :=
    (mem_insert_iff.mp (hIB' (mem_insert _ _))).elim id fun h' => (hf (diff_subset _ _ h')).elim
  rwa [this]

theorem Base.exchange_base_of_indep' (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.indep (insert f B \ {e})) : M.base (insert f B \ {e}) :=
  by
  have hfe : f ≠ e := by
    rintro rfl
    exact hf he
  rw [← insert_diff_singleton_comm hfe] at *
  exact hB.exchange_base_of_indep he hf hI

/-- If the difference of two bases is a singleton, then they differ by an insertion/removal -/
theorem Base.eq_exchange_of_diff_eq_singleton (hB : M.base B) (hB' : M.base B') (h : B \ B' = {e}) :
    ∃ f ∈ B' \ B, B' = insert f B \ {e} :=
  by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by
    rintro rfl
    exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_diff_singleton_comm hne] at hb
  refine' ⟨f, hf, (hb.eq_of_subset_base hB' _).symm⟩
  rw [diff_subset_iff, insert_subset, union_comm, ← diff_subset_iff, h, and_iff_left subset.rfl]
  exact Or.inl hf.1

theorem Basis.indep (hI : M.Basis I X) : M.indep I :=
  hI.1.1

theorem Basis.subset (hI : M.Basis I X) : I ⊆ X :=
  hI.1.2

theorem Basis.eq_of_subset_indep (hI : M.Basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
    I = J :=
  hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

theorem Basis.finite (hI : M.Basis I X) [FiniteRk M] : I.Finite :=
  hI.indep.Finite

theorem basis_iff : M.Basis I X ↔ M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J :=
  ⟨fun h => ⟨h.indep, h.Subset, fun _ => h.eq_of_subset_indep⟩, fun h =>
    ⟨⟨h.1, h.2.1⟩, fun J hJ hIJ => (h.2.2 _ hJ.1 hIJ hJ.2).symm.Subset⟩⟩

theorem Indep.basis_of_maximal_subset (hI : M.indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.indep J → I ⊆ J → J ⊆ X → J ⊆ I) : M.Basis I X :=
  ⟨⟨hI, hIX⟩, fun J hJ hIJ => hmax hJ.1 hIJ hJ.2⟩

@[simp]
theorem basis_empty_iff (M : Matroid E) : M.Basis I ∅ ↔ I = ∅ :=
  by
  refine' ⟨fun h => subset_empty_iff.mp h.Subset, _⟩
  rintro rfl
  exact ⟨⟨M.empty_indep, empty_subset _⟩, fun J h h' => h.2⟩

theorem Basis.basis_subset (hI : M.Basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.Basis I Y :=
  ⟨⟨hI.indep, hIY⟩, fun J hJ hIJ => hI.2 ⟨hJ.1, hJ.2.trans hYX⟩ hIJ⟩

theorem Basis.dep_of_sSubset (hI : M.Basis I X) {Y : Set E} (hIY : I ⊂ Y) (hYX : Y ⊆ X) :
    ¬M.indep Y := fun hY => hIY.Ne (hI.eq_of_subset_indep hY hIY.Subset hYX)

theorem Basis.insert_dep (hI : M.Basis I X) (he : e ∈ X \ I) : ¬M.indep (insert e I) :=
  hI.dep_of_sSubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1, hI.Subset⟩)

theorem Basis.mem_of_insert_indep (hI : M.Basis I X) (he : e ∈ X) (hIe : M.indep (insert e I)) :
    e ∈ I :=
  by_contra fun heI => hI.insert_dep ⟨he, heI⟩ hIe

theorem Basis.not_basis_of_sSubset (hI : M.Basis I X) (hJI : J ⊂ I) : ¬M.Basis J X := fun h =>
  hJI.Ne (h.eq_of_subset_indep hI.indep hJI.Subset hI.Subset)

theorem Indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) : ∃ J, M.Basis J X ∧ I ⊆ J :=
  by
  obtain ⟨J, ⟨hJ : M.indep J, hIJ, hJX⟩, hJmax⟩ := M.maximality I X hI hIX
  exact ⟨J, ⟨⟨hJ, hJX⟩, fun K hK hJK => hJmax ⟨hK.1, hIJ.trans hJK, hK.2⟩ hJK⟩, hIJ⟩

theorem Indep.eq_of_basis (hI : M.indep I) (hJ : M.Basis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.Subset Subset.rfl

theorem Indep.basis_self (hI : M.indep I) : M.Basis I I :=
  ⟨⟨hI, rfl.Subset⟩, fun J hJ _ => hJ.2⟩

@[simp]
theorem basis_self_iff_indep : M.Basis I I ↔ M.indep I :=
  ⟨Basis.indep, Indep.basis_self⟩

theorem exists_basis (M : Matroid E) (X : Set E) : ∃ I, M.Basis I X :=
  by
  obtain ⟨I, hI, -⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X)
  exact ⟨_, hI⟩

theorem Basis.exists_base (hI : M.Basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
  by
  obtain ⟨B, hB, hIB⟩ := hI.indep
  refine' ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩
  rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
      (inter_subset_right _ _)]

theorem base_iff_basis_univ : M.base B ↔ M.Basis B univ :=
  by
  rw [base_iff_maximal_indep, basis_iff]
  simp

theorem Base.basis_univ (hB : M.base B) : M.Basis B univ :=
  base_iff_basis_univ.mp hB

theorem Indep.basis_of_forall_insert (hI : M.indep I) (hIX : I ⊆ X)
    (he : ∀ e ∈ X \ I, ¬M.indep (insert e I)) : M.Basis I X :=
  ⟨⟨hI, hIX⟩, fun J hJ hIJ e heJ =>
    by_contra fun heI => he _ ⟨hJ.2 heJ, heI⟩ (hJ.1.Subset (insert_subset.mpr ⟨heJ, hIJ⟩))⟩

theorem Basis.iUnion_basis_iUnion {ι : Type _} (X I : ι → Set E) (hI : ∀ i, M.Basis (I i) (X i))
    (h_ind : M.indep (⋃ i, I i)) : M.Basis (⋃ i, I i) (⋃ i, X i) :=
  by
  refine'
    h_ind.basis_of_forall_insert
      (Union_subset_iff.mpr fun i => (hI i).Subset.trans (subset_Union _ _)) fun e he hi => _
  simp only [mem_diff, mem_Union, not_exists] at he
  obtain ⟨i, heXi⟩ := he.1
  exact
    he.2 i ((hI i).mem_of_insert_indep heXi (hi.subset (insert_subset_insert (subset_Union _ _))))

theorem Basis.basis_iUnion {ι : Type _} [Nonempty ι] (X : ι → Set E) (hI : ∀ i, M.Basis I (X i)) :
    M.Basis I (⋃ i, X i) :=
  by
  convert basis.Union_basis_Union X (fun _ => I) (fun i => hI i) _
  all_goals rw [Union_const]
  exact (hI ‹Nonempty ι›.some).indep

theorem Basis.union_basis_union (hIX : M.Basis I X) (hJY : M.Basis J Y) (h : M.indep (I ∪ J)) :
    M.Basis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_Union, union_eq_Union]
  refine' basis.Union_basis_Union _ _ _ _
  · simp only [Bool.forall_bool, Bool.cond_false, Bool.cond_true]
    exact ⟨hJY, hIX⟩
  rwa [← union_eq_Union]

theorem Basis.basis_union (hIX : M.Basis I X) (hIY : M.Basis I Y) : M.Basis I (X ∪ Y) :=
  by
  convert hIX.union_basis_union hIY _ <;> rw [union_self]
  exact hIX.indep

theorem Basis.basis_union_of_subset (hI : M.Basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) :
    M.Basis J (J ∪ X) :=
  by
  convert hJ.basis_self.union_basis_union hI (by rwa [union_eq_left_iff_subset.mpr hIJ])
  rw [union_eq_left_iff_subset.mpr hIJ]

theorem Basis.insert_basis_insert (hI : M.Basis I X) (h : M.indep (insert e I)) :
    M.Basis (insert e I) (insert e X) :=
  by
  convert hI.union_basis_union
      (indep.basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _
  simp; simp; simpa

theorem Base.insert_dep (hB : M.base B) (h : e ∉ B) : ¬M.indep (insert e B) := fun h' =>
  (insert_ne_self.mpr h).symm ((base_iff_maximal_indep.mp hB).2 _ h' (subset_insert _ _))

theorem Base.sSubset_dep (hB : M.base B) (h : B ⊂ X) : ¬M.indep X := fun h' =>
  h.Ne ((base_iff_maximal_indep.mp hB).2 _ h' h.Subset)

theorem Indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) :
    ∃ e ∈ B \ I, M.indep (insert e I) :=
  by
  obtain ⟨B', hB', hIB'⟩ := hI
  obtain ⟨x, hxB', hx⟩ :=
    exists_of_ssubset
      (hIB'.ssubset_of_ne
        (by
          rintro rfl
          exact hI' hB'))
  obtain hxB | hxB := em (x ∈ B)
  · exact ⟨x, ⟨hxB, hx⟩, ⟨B', hB', insert_subset.mpr ⟨hxB', hIB'⟩⟩⟩
  obtain ⟨e, he, hbase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact
    ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩,
      ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩

theorem Base.exists_insert_of_sSubset (hB : M.base B) (hIB : I ⊂ B) (hB' : M.base B') :
    ∃ e ∈ B' \ I, M.indep (insert e I) :=
  (hB.indep.Subset hIB.Subset).exists_insert_of_not_base
    (fun hI => hIB.Ne (hI.eq_of_subset_base hB hIB.Subset)) hB'

theorem Base.base_of_basis_supset (hB : M.base B) (hBX : B ⊆ X) (hIX : M.Basis I X) : M.base I :=
  by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_base h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

theorem Base.basis_of_subset (hB : M.base B) (hBX : B ⊆ X) : M.Basis B X :=
  ⟨⟨hB.indep, hBX⟩, fun J hJ hBJ => by rw [hB.eq_of_subset_indep hJ.1 hBJ]⟩

theorem Indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) :
    ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
  by
  obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset (subset_union_left I B)
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩

theorem eq_of_indep_iff_indep_forall {M₁ M₂ : Matroid E} (h : ∀ I, M₁.indep I ↔ M₂.indep I) :
    M₁ = M₂ := by
  ext B
  have hI : M₁.indep = M₂.indep := by
    ext
    apply h
  simp_rw [base_iff_maximal_indep, hI]

theorem eq_iff_indep_iff_indep_forall {M₁ M₂ : Matroid E} :
    M₁ = M₂ ↔ ∀ I, M₁.indep I ↔ M₂.indep I :=
  ⟨fun h I => by rw [h], eq_of_indep_iff_indep_forall⟩

theorem eq_iff_setOf_indep_eq_setOf_indep {M₁ M₂ : Matroid E} :
    M₁ = M₂ ↔ { I | M₁.indep I } = { I | M₂.indep I } :=
  by
  rw [eq_iff_indep_iff_indep_forall, Set.ext_iff]
  rfl

end Indep

section FromAxioms

def matroidOfBase {E : Type _} (base : Set E → Prop) (exists_base : ∃ B, base B)
    (base_exchange : ExchangeProperty base)
    (maximality : ExistsMaximalSubsetProperty { I | ∃ B, base B ∧ I ⊆ B }) : Matroid E :=
  ⟨base, exists_base, base_exchange, maximality⟩

@[simp]
theorem matroidOfBase_apply {E : Type _} (base : Set E → Prop) (exists_base : ∃ B, base B)
    (base_exchange : ExchangeProperty base)
    (maximality : ExistsMaximalSubsetProperty { I | ∃ B, base B ∧ I ⊆ B }) :
    (matroidOfBase base exists_base base_exchange maximality).base = base :=
  rfl

/-- A collection of bases with the exchange property and at least one finite member is a matroid -/
def matroidOfExistsFiniteBase {E : Type _} (base : Set E → Prop)
    (exists_finite_base : ∃ B, base B ∧ B.Finite) (base_exchange : ExchangeProperty base) :
    Matroid E :=
  matroidOfBase base
    (let ⟨B, h⟩ := exists_finite_base
    ⟨B, h.1⟩)
    base_exchange
    (by
      obtain ⟨B, hB, hfin⟩ := exists_finite_base
      apply existsMaximalSubsetProperty_of_bounded ⟨B.ncard, _⟩
      rintro I ⟨B', hB', hIB'⟩
      have hB'fin : B'.finite := finite_of_finite_of_exch base_exchange hB hB' hfin
      rw [card_eq_card_of_exchange base_exchange hB hB']
      exact ⟨hB'fin.subset hIB', ncard_le_of_subset hIB' hB'fin⟩)

@[simp]
theorem matroidOfExistsFiniteBase_apply {E : Type _} (base : Set E → Prop)
    (exists_finite_base : ∃ B, base B ∧ B.Finite) (base_exchange : ExchangeProperty base) :
    (matroidOfExistsFiniteBase base exists_finite_base base_exchange).base = base :=
  rfl

/-- A matroid constructed with a finite base is `finite_rk` -/
instance {E : Type _} {base : Set E → Prop} {exists_finite_base : ∃ B, base B ∧ B.Finite}
    {base_exchange : ExchangeProperty base} :
    Matroid.FiniteRk (matroidOfExistsFiniteBase base exists_finite_base base_exchange) :=
  ⟨exists_finite_base⟩

def matroidOfBaseOfFinite {E : Type _} [Finite E] (base : Set E → Prop) (exists_base : ∃ B, base B)
    (base_exchange : ExchangeProperty base) : Matroid E :=
  matroidOfExistsFiniteBase base
    (let ⟨B, hB⟩ := exists_base
    ⟨B, hB, toFinite _⟩)
    base_exchange

@[simp]
theorem matroidOfBaseOfFinite_apply {E : Type _} [Finite E] (base : Set E → Prop)
    (exists_base : ∃ B, base B) (base_exchange : ExchangeProperty base) :
    (matroidOfBaseOfFinite base exists_base base_exchange).base = base :=
  rfl

/-- A version of the independence axioms that avoids cardinality -/
def matroidOfIndep {E : Type _} (indep : Set E → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_maximal : ExistsMaximalSubsetProperty indep) : Matroid E :=
  matroidOfBase (fun B => B ∈ maximals (· ⊆ ·) indep)
    (by
      obtain ⟨B, ⟨hB, -, -⟩, hB₁⟩ := h_maximal ∅ univ h_empty (subset_univ _)
      exact ⟨B, ⟨hB, fun B' hB' hBB' => hB₁ ⟨hB', empty_subset _, subset_univ _⟩ hBB'⟩⟩)
    (by
      rintro B B' ⟨hB, hBmax⟩ ⟨hB', hB'max⟩ e he
      obtain ⟨f, hf, hfB⟩ := h_aug (h_subset hB (diff_subset B {e})) _ ⟨hB', hB'max⟩
      simp only [mem_diff, mem_singleton_iff, not_and, Classical.not_not] at hf
      have hfB' : f ∉ B := by
        intro hfB
        have := hf.2 hfB
        subst this
        exact he.2 hf.1
      · refine' ⟨f, ⟨hf.1, hfB'⟩, by_contra fun hnot => _⟩
        obtain ⟨x, hxB, hind⟩ := h_aug hfB hnot ⟨hB, hBmax⟩
        simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or, not_and,
          Classical.not_not] at hxB
        have := hxB.2.2 hxB.1
        subst this
        rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind
        exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _)
      simp only [maximals, mem_sep_iff, diff_singleton_subset_iff, not_and, not_forall, exists_prop]
      exact fun _ => ⟨B, hB, subset_insert _ _, fun hss => (hss he.1).2 rfl⟩)
    (by
      rintro I X ⟨B, hB, hIB⟩ hIX
      obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal I X (h_subset hB.1 hIB) hIX
      obtain ⟨BJ, hBJ⟩ := h_maximal J univ hJ (subset_univ _)
      refine' ⟨J, ⟨⟨BJ, _, hBJ.1.2.1⟩, hIJ, hJX⟩, _⟩
      · exact ⟨hBJ.1.1, fun B' hB' hBJB' => hBJ.2 ⟨hB', hBJ.1.2.1.trans hBJB', subset_univ _⟩ hBJB'⟩
      simp only [mem_set_of_eq, and_imp, forall_exists_index]
      rintro A ⟨B', ⟨hB'i : indep _, hB'max⟩, hB''⟩ hIA hAX hJA
      exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA)

@[simp]
theorem matroidOfIndep_apply {E : Type _} (indep : Set E → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_maximal : ExistsMaximalSubsetProperty indep) :
    (matroidOfIndep indep h_empty h_subset h_aug h_maximal).indep = indep :=
  by
  ext I
  simp only [Matroid.Indep, matroid_of_indep]
  refine' ⟨fun ⟨B, hB, hIB⟩ => h_subset hB.1 hIB, fun hI => _⟩
  obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ := h_maximal I univ hI (subset_univ _)
  exact ⟨B, ⟨hB, fun B' hB' hBB' => hBmax ⟨hB', hIB.trans hBB', subset_univ _⟩ hBB'⟩, hIB⟩

/-- If there is an absolute upper bound on the size of an independent set, then the maximality
  axiom isn't needed to define a matroid by independent sets. -/
def matroidOfIndepOfBdd {E : Type _} (indep : Set E → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) : Matroid E :=
  matroidOfIndep indep h_empty h_subset h_aug (existsMaximalSubsetProperty_of_bounded h_bdd)

@[simp]
theorem matroidOfIndepOfBdd_apply (indep : Set E → Prop) (h_empty : indep ∅)
    (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) :
    (matroidOfIndepOfBdd indep h_empty h_subset h_aug h_bdd).indep = indep := by
  simp [matroid_of_indep_of_bdd]

instance (indep : Set E → Prop) (h_empty : indep ∅) (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (h_aug :
      ∀ ⦃I B⦄,
        indep I →
          I ∉ maximals (· ⊆ ·) indep → B ∈ maximals (· ⊆ ·) indep → ∃ x ∈ B \ I, indep (insert x I))
    (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n) :
    Matroid.FiniteRk (matroidOfIndepOfBdd indep h_empty h_subset h_aug h_bdd) :=
  by
  obtain ⟨B, hB⟩ := (matroid_of_indep_of_bdd indep h_empty h_subset h_aug h_bdd).exists_base
  obtain ⟨h, h_bdd⟩ := h_bdd
  refine' hB.finite_rk_of_finite (h_bdd B _).1
  rw [← matroid_of_indep_of_bdd_apply indep, Matroid.Indep]
  exact ⟨_, hB, subset.rfl⟩

/-- A collection of sets in a finite type satisfying the usual independence axioms determines a
  matroid -/
def matroidOfIndepOfFinite [Finite E] (indep : Set E → Prop) (exists_ind : ∃ I, indep I)
    (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (ind_aug :
      ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) :
    Matroid E :=
  matroidOfIndep indep (Exists.elim exists_ind fun I hI => ind_mono hI (empty_subset _)) ind_mono
    (by
      intro I J hI hIn hJ
      by_contra' h'
      obtain hlt | hle := lt_or_le I.ncard J.ncard
      · obtain ⟨e, heJ, heI, hi⟩ := ind_aug hI hJ.1 hlt
        exact h' e ⟨heJ, heI⟩ hi
      obtain h_eq | hlt := hle.eq_or_lt
      · refine'
          hIn
            ⟨hI, fun K (hK : indep K) hIK =>
              hIK.ssubset_or_eq.elim (fun hss => _) fun h => h.symm.subset⟩
        obtain ⟨f, hfK, hfJ, hi⟩ := ind_aug hJ.1 hK (h_eq.trans_lt (ncard_lt_ncard hss))
        exact (hfJ (hJ.2 hi (subset_insert _ _) (mem_insert f _))).elim
      obtain ⟨e, heI, heJ, hi⟩ := ind_aug hJ.1 hI hlt
      exact heJ (hJ.2 hi (subset_insert _ _) (mem_insert e _)))
    (existsMaximalSubsetProperty_of_bounded
      ⟨(univ : Set E).ncard, fun I hI => ⟨toFinite I, ncard_le_of_subset (subset_univ _)⟩⟩)

@[simp]
theorem matroidOfIndepOfFinite_apply [Finite E] {indep : Set E → Prop} (exists_ind : ∃ I, indep I)
    (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
    (ind_aug :
      ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) :
    (matroidOfIndepOfFinite indep exists_ind ind_mono ind_aug).indep = indep := by
  simp [matroid_of_indep_of_finite]

end FromAxioms

section Dual

/-- This is really an order-theory lemma. Not clear where to put it, though.  -/
theorem base_compl_iff_mem_maximals_disjoint_base :
    M.base (Bᶜ) ↔ B ∈ maximals (· ⊆ ·) { I | ∃ B, M.base B ∧ Disjoint I B } :=
  by
  simp_rw [← subset_compl_iff_disjoint_left]
  refine' ⟨fun h => ⟨⟨Bᶜ, h, subset.rfl⟩, _⟩, _⟩
  · rintro X ⟨B', hB', hXB'⟩ hBX
    rw [← compl_subset_compl] at hBX⊢
    rwa [← hB'.eq_of_subset_base h (hXB'.trans hBX)]
  rintro ⟨⟨B', hB', hBB'⟩, h⟩
  rw [subset_compl_comm] at hBB'
  rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl]
  rw [compl_compl]

/-- The dual of a matroid `M`; its bases are the complements of bases in `M`.
  The proofs here are messier than they need to be. -/
def dual (M : Matroid E) : Matroid E :=
  matroidOfIndep (fun I => ∃ B, M.base B ∧ Disjoint I B)
    (M.exists_base.imp fun B hB => ⟨hB, empty_disjoint B⟩)
    (fun I J ⟨B, hB, hJB⟩ hIJ => ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩)
    (by
      rintro I X ⟨B, hB, hIB⟩ hI_not_max hX_max
      have hB' := base_compl_iff_mem_maximals_disjoint_base.mpr hX_max
      set B' := Xᶜ with hX
      have hI := (not_iff_not.mpr base_compl_iff_mem_maximals_disjoint_base).mpr hI_not_max
      obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB
      rw [← compl_subset_compl, ← hIB.sdiff_eq_right, ← union_diff_distrib, diff_eq, compl_inter,
        compl_compl, union_subset_iff, compl_subset_compl] at hB''₂
      obtain ⟨e, ⟨heB'', heI⟩⟩ :=
        exists_of_ssubset
          (hB''₂.2.ssubset_of_ne
            (by
              rintro rfl
              rw [compl_compl] at hI
              exact hI hB''))
      refine' ⟨e, ⟨by_contra fun heB' => heB'' (hB''₁ ⟨heB', heI⟩), heI⟩, ⟨B'', hB'', _⟩⟩
      rw [← union_singleton, disjoint_union_left, disjoint_singleton_left, ←
        subset_compl_iff_disjoint_right]
      exact ⟨hB''₂.2, heB''⟩)
    (by
      rintro I' X ⟨B, hB, hI'B⟩ hI'X
      obtain ⟨I, hI⟩ := M.exists_basis (Xᶜ)
      obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB
      refine'
        ⟨X \ B', ⟨⟨_, hB', disjoint_sdiff_left⟩, subset_diff.mpr ⟨hI'X, _⟩, diff_subset _ _⟩, _⟩
      · refine' disjoint_of_subset_right hB'IB (disjoint_union_right.mpr ⟨_, hI'B⟩)
        rw [← subset_compl_iff_disjoint_left]
        exact hI.subset.trans (compl_subset_compl.mpr hI'X)
      rintro J ⟨⟨B'', hB'', hJB''⟩, hI'J, hJX⟩ hXB'J
      have hI' : B'' ∩ X ∪ B' \ X ⊆ B' :=
        by
        refine' union_subset _ (diff_subset _ _)
        refine' (inter_subset_inter_right _ (diff_subset_iff.mp hXB'J)).trans _
        rw [inter_distrib_left, inter_comm _ J, disjoint_iff_inter_eq_empty.mp hJB'', union_empty]
        exact inter_subset_right _ _
      obtain ⟨B₁, hB₁, hI'B₁, hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB''
      rw [union_comm, ← union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I
      have : B₁ = B' := by
        refine' hB₁.eq_of_subset_indep hB'.indep fun e he => _
        refine' (hB₁I he).elim (fun heB'' => _) fun h => h.1
        refine' (em (e ∈ X)).elim (fun heX => hI' (Or.inl ⟨heB'', heX⟩)) fun heX => hIB' _
        refine' hI.mem_of_insert_indep heX (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩))
        refine' (subset_union_of_subset_right (subset_diff.mpr ⟨hIB', _⟩) _).trans hI'B₁
        exact subset_compl_iff_disjoint_right.mp hI.subset
      subst this
      refine' subset_diff.mpr ⟨hJX, by_contra fun hne => _⟩
      obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne
      obtain heB'' | ⟨heB₁, heX⟩ := hB₁I heB'
      · exact hJB''.ne_of_mem heJ heB'' rfl
      exact heX (hJX heJ))

/-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. -/
@[class]
structure HasMatroidDual (α : Type _) where
  dual : α → α

/- ./././Mathport/Syntax/Translate/Command.lean:476:9: unsupported: advanced prec syntax «expr + »(max[std.prec.max], 1) -/
-- mathport name: «expr ﹡»
postfix:999 "﹡" => HasMatroidDual.dual

instance matroidDual {E : Type _} : HasMatroidDual (Matroid E) :=
  ⟨Matroid.dual⟩

theorem dual.base_iff : M﹡.base B ↔ M.base (Bᶜ) :=
  base_compl_iff_mem_maximals_disjoint_base.symm

@[simp]
theorem dual_dual (M : Matroid E) : M﹡﹡ = M := by
  ext
  simp_rw [dual.base_iff, compl_compl]

theorem dual_indep_iff_coindep : M﹡.indep X ↔ M.Coindep X := by
  simp [has_matroid_dual.dual, dual, coindep]

theorem Base.compl_base_dual (hB : M.base B) : M﹡.base (Bᶜ) := by rwa [dual.base_iff, compl_compl]

theorem Base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.Basis (B ∩ X) X) :
    M﹡.Basis (Bᶜ ∩ Xᶜ) (Xᶜ) := by
  rw [basis_iff]
  refine'
    ⟨hB.compl_base_dual.indep.subset (inter_subset_left _ _), inter_subset_right _ _,
      fun J hJ hBCJ hJX => hBCJ.antisymm (subset_inter (fun e heJ heB => _) hJX)⟩
  obtain ⟨B', hB', hJB'⟩ := dual_indep_iff_coindep.mp hJ
  obtain ⟨B'', hB'', hsB'', hB''s⟩ := hBX.indep.exists_base_subset_union_base hB'
  have hB'ss : B' ⊆ B ∪ X :=
    by
    rw [← compl_subset_compl, compl_union, subset_compl_iff_disjoint_right]
    exact disjoint_of_subset_left hBCJ hJB'
  have hB''ss : B'' ⊆ B :=
    by
    refine' fun e he => (hB''s he).elim And.left fun heB' => (hB'ss heB').elim id fun heX => _
    exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he, hsB''⟩))).1
  have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm
  subst this
  exact (hB''s heB).elim (fun heBX => hJX heJ heBX.2) fun heB' => hJB'.ne_of_mem heJ heB' rfl

theorem Base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B) :
    M.Basis (B ∩ X) X ↔ M﹡.Basis (Bᶜ ∩ Xᶜ) (Xᶜ) :=
  ⟨hB.compl_inter_basis_of_inter_basis, fun h => by
    simpa using hB.compl_base_dual.compl_inter_basis_of_inter_basis h⟩

theorem dual_inj {M₁ M₂ : Matroid E} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
  by
  ext B
  rw [← compl_compl B, ← dual.base_iff, h, dual.base_iff]

@[simp]
theorem dual_inj_iff {M₁ M₂ : Matroid E} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ :=
  ⟨dual_inj, congr_arg _⟩

theorem coindep_iff_disjoint_base : M.Coindep X ↔ ∃ B, M.base B ∧ Disjoint X B :=
  Iff.rfl

theorem Coindep.exists_disjoint_base (hX : M.Coindep X) : ∃ B, M.base B ∧ Disjoint X B :=
  hX

theorem Coindep.base_of_basis_compl (hX : M.Coindep X) (hB : M.Basis B (Xᶜ)) : M.base B :=
  by
  obtain ⟨B', hB'⟩ := hX.exists_disjoint_base
  exact hB'.1.base_of_basis_supset (subset_compl_iff_disjoint_left.mpr hB'.2) hB

theorem base_iff_dual_base_compl : M.base B ↔ M﹡.base (Bᶜ) := by
  rw [← compl_compl B, dual.base_iff, compl_compl, compl_compl]

end Dual

section Lrestrict

/-- Turn all elements of the matroid outside `X` into loops -/
def lrestrict (M : Matroid E) (X : Set E) : Matroid E :=
  matroidOfIndep (fun I => M.indep I ∧ I ⊆ X) ⟨M.empty_indep, empty_subset _⟩
    (fun I J hJ hIJ => ⟨hJ.1.Subset hIJ, hIJ.trans hJ.2⟩)
    (by
      rintro I I' ⟨hI, hIX⟩ (hIn : ¬M.basis I X) (hI' : M.basis I' X)
      obtain ⟨B', hB', rfl⟩ := hI'.exists_base
      obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB'
      rw [hB'.inter_basis_iff_compl_inter_basis_dual] at hI'
      have hss : B'ᶜ ∩ Xᶜ ⊆ Bᶜ ∩ Xᶜ :=
        by
        rw [← compl_union, ← compl_union, compl_subset_compl]
        exact
          union_subset
            (hBIB'.trans
              (union_subset (hIX.trans (subset_union_right _ _)) (subset_union_left _ _)))
            (subset_union_right _ _)
      have h_eq := hI'.eq_of_subset_indep _ hss (inter_subset_right _ _)
      · rw [h_eq, ← hB.inter_basis_iff_compl_inter_basis_dual] at hI'
        have hssu : I ⊂ B ∩ X :=
          (subset_inter hIB hIX).ssubset_of_ne
            (by
              rintro rfl
              exact hIn hI')
        obtain ⟨e, he, heI⟩ := exists_of_ssubset hssu
        refine'
          ⟨e, ⟨⟨_, he.2⟩, heI⟩, hI'.indep.subset (insert_subset.mpr ⟨he, hssu.subset⟩),
            insert_subset.mpr ⟨he.2, hIX⟩⟩
        exact (hBIB' he.1).elim (fun heI' => (heI heI').elim) id
      exact
        dual_indep_iff_coindep.mpr
          ⟨B, hB, disjoint_of_subset_left (inter_subset_left _ _) disjoint_compl_left⟩)
    (by
      rintro I A ⟨hI, hIX⟩ hIA
      obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIX hIA)
      refine'
        ⟨J,
          ⟨⟨hJ.indep, hJ.subset.trans (inter_subset_left _ _)⟩, hIJ,
            hJ.subset.trans (inter_subset_right _ _)⟩,
          fun K hK hJK => _⟩
      rw [hJ.eq_of_subset_indep hK.1.1 hJK (subset_inter hK.1.2 hK.2.2)])

/- The minimal API below is private because it is later developed with appropriate notation in
  `pseudominor.lean` -/
theorem lrestrict_indep_iff : (M.lrestrict X).indep I ↔ M.indep I ∧ I ⊆ X := by simp [lrestrict]

private theorem lrestrict_lrestrict : (M.lrestrict X).lrestrict Y = M.lrestrict (X ∩ Y) :=
  eq_of_indep_iff_indep_forall fun I => by
    simp only [and_assoc', lrestrict_indep_iff, subset_inter_iff]

private theorem lrestrict_lrestrict_subset (hXY : X ⊆ Y) :
    (M.lrestrict Y).lrestrict X = M.lrestrict X := by
  rw [lrestrict_lrestrict, inter_eq_right_iff_subset.mpr hXY]

private theorem indep.indep_lrestrict_of_subset (hI : M.indep I) (hIX : I ⊆ X) :
    (M.lrestrict X).indep I :=
  lrestrict_indep_iff.mpr ⟨hI, hIX⟩

private theorem lrestrict_base_iff : (M.lrestrict X).base I ↔ M.Basis I X :=
  Iff.rfl

private theorem basis.base_lrestrict (h : M.Basis I X) : (M.lrestrict X).base I :=
  lrestrict_base_iff.mpr h

private theorem basis.basis_lrestrict_of_subset (hI : M.Basis I X) (hXY : X ⊆ Y) :
    (M.lrestrict Y).Basis I X := by
  rwa [← lrestrict_base_iff, lrestrict_lrestrict_subset hXY, lrestrict_base_iff]

end Lrestrict

section Basis

theorem Basis.transfer (hIX : M.Basis I X) (hJX : M.Basis J X) (hXY : X ⊆ Y) (hJY : M.Basis J Y) :
    M.Basis I Y := by
  rw [← lrestrict_base_iff] at hJY⊢
  exact hJY.base_of_basis_supset hJX.subset (basis.basis_lrestrict_of_subset hIX hXY)

theorem Basis.transfer' (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X) (hIY : I ⊆ Y) :
    M.Basis I Y :=
  by
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _)
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _)
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ

theorem Basis.transfer'' (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X) : M.Basis I (I ∪ Y) :=
  by
  obtain ⟨J', hJ', hJJ'⟩ := hJ.indep.subset_basis_of_subset hJX
  have hJ'Y := (hJ.basis_union_of_subset hJ'.indep hJJ').basis_union hJ'
  refine' (hI.transfer' hJ'Y hJ'.subset _).basis_subset _ _
  · exact subset_union_of_subset_right hI.subset _
  · exact subset_union_left _ _
  refine' union_subset (subset_union_of_subset_right hI.subset _) _
  rw [union_right_comm]
  exact subset_union_right _ _

theorem Indep.exists_basis_subset_union_basis (hI : M.indep I) (hIX : I ⊆ X) (hJ : M.Basis J X) :
    ∃ I', M.Basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J :=
  by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (indep.indep_lrestrict_of_subset hI hIX).exists_base_subset_union_base (basis.base_lrestrict hJ)
  exact ⟨I', lrestrict_base_iff.mp hI', hII', hI'IJ⟩

theorem Indep.exists_insert_of_not_basis (hI : M.indep I) (hIX : I ⊆ X) (hI' : ¬M.Basis I X)
    (hJ : M.Basis J X) : ∃ e ∈ J \ I, M.indep (insert e I) :=
  by
  rw [← lrestrict_base_iff] at hI' hJ
  obtain ⟨e, he, hi⟩ := (indep.indep_lrestrict_of_subset hI hIX).exists_insert_of_not_base hI' hJ
  exact ⟨e, he, (lrestrict_indep_iff.mp hi).1⟩

theorem Basis.base_of_base_subset (hIX : M.Basis I X) (hB : M.base B) (hBX : B ⊆ X) : M.base I :=
  hB.base_of_basis_supset hBX hIX

theorem Basis.exchange (hIX : M.Basis I X) (hJX : M.Basis J X) (he : e ∈ I \ J) :
    ∃ f ∈ J \ I, M.Basis (insert f (I \ {e})) X :=
  by
  simp_rw [← lrestrict_base_iff] at *
  exact hIX.exchange hJX he

theorem Basis.eq_exchange_of_diff_eq_singleton (hI : M.Basis I X) (hJ : M.Basis J X)
    (hIJ : I \ J = {e}) : ∃ f ∈ J \ I, J = insert f I \ {e} :=
  by
  rw [← lrestrict_base_iff] at hI hJ
  exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ

end Basis

section Finite

theorem Basis.card_eq_card_of_basis (hIX : M.Basis I X) (hJX : M.Basis J X) : I.ncard = J.ncard :=
  by
  rw [← lrestrict_base_iff] at hIX hJX
  exact hIX.card_eq_card_of_base hJX

theorem Basis.finite_of_finite (hIX : M.Basis I X) (hI : I.Finite) (hJX : M.Basis J X) : J.Finite :=
  by
  rw [← lrestrict_base_iff] at hIX hJX
  exact hIX.finite_of_finite hI hJX

theorem Basis.infinite_of_infinite (hIX : M.Basis I X) (hI : I.Infinite) (hJX : M.Basis J X) :
    J.Infinite := by
  rw [← lrestrict_base_iff] at hIX hJX
  exact hIX.infinite_of_infinite hI hJX

theorem Basis.card_diff_comm (hI : M.Basis I X) (hJ : M.Basis J X) :
    (I \ J).ncard = (J \ I).ncard :=
  by
  rw [← lrestrict_base_iff] at hI hJ
  rw [hJ.card_diff_comm hI]

theorem Basis.diff_finite_comm (hIX : M.Basis I X) (hJX : M.Basis J X) :
    (I \ J).Finite ↔ (J \ I).Finite :=
  by
  rw [← lrestrict_base_iff] at hIX hJX
  exact hIX.diff_finite_comm hJX

theorem Basis.diff_infinite_comm (hIX : M.Basis I X) (hJX : M.Basis J X) :
    (I \ J).Infinite ↔ (J \ I).Infinite :=
  by
  rw [← lrestrict_base_iff] at hIX hJX
  exact hIX.diff_infinite_comm hJX

theorem Indep.augment_of_finite (hI : M.indep I) (hJ : M.indep J) (hIfin : I.Finite)
    (hIJ : I.ncard < J.ncard) : ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
  by
  obtain ⟨K, hK, hIK⟩ :=
    (indep.indep_lrestrict_of_subset hI (subset_union_left I J)).exists_base_supset
  obtain ⟨K', hK', hJK'⟩ :=
    (indep.indep_lrestrict_of_subset hJ (subset_union_right I J)).exists_base_supset
  have hJfin := finite_of_ncard_pos ((Nat.zero_le _).trans_lt hIJ)
  rw [lrestrict_base_iff] at hK hK'
  have hK'fin := (hIfin.union hJfin).Subset hK'.subset
  have hlt :=
    hIJ.trans_le ((ncard_le_of_subset hJK' hK'fin).trans_eq (hK'.card_eq_card_of_basis hK))
  obtain ⟨e, he⟩ := exists_mem_not_mem_of_ncard_lt_ncard hlt hIfin
  exact
    ⟨e, (hK.subset he.1).elim (False.elim ∘ he.2) id, he.2,
      hK.indep.subset (insert_subset.mpr ⟨he.1, hIK⟩)⟩

/-- The independence augmentation axiom; given independent sets `I,J` with `I` smaller than `J`,
  there is an element `e` of `J \ I` whose insertion into `e` gives an independent set.  -/
theorem Indep.augment [FiniteRk M] (hI : M.indep I) (hJ : M.indep J) (hIJ : I.ncard < J.ncard) :
    ∃ x ∈ J, x ∉ I ∧ M.indep (insert x I) :=
  hI.augment_of_finite hJ hI.Finite hIJ

/-- The independence augmentation axiom in a form that finds a strict superset -/
theorem Indep.sSubset_indep_of_card_lt_of_finite (hI : M.indep I) (hI_fin : I.Finite)
    (hJ : M.indep J) (hIJ : I.ncard < J.ncard) : ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
  by
  obtain ⟨e, heJ, heI, hI'⟩ := hI.augment_of_finite hJ hI_fin hIJ
  exact ⟨_, hI', ssubset_insert heI, insert_subset.mpr ⟨Or.inr heJ, subset_union_left _ _⟩⟩

theorem Indep.sSubset_indep_of_card_lt [FiniteRk M] (hI : M.indep I) (hJ : M.indep J)
    (hIJ : I.ncard < J.ncard) : ∃ I', M.indep I' ∧ I ⊂ I' ∧ I' ⊆ I ∪ J :=
  hI.sSubset_indep_of_card_lt_of_finite hI.Finite hJ hIJ

theorem Indep.le_card_basis [FiniteRk M] (hI : M.indep I) (hIX : I ⊆ X) (hJX : M.Basis J X) :
    I.ncard ≤ J.ncard := by
  refine' le_of_not_lt fun hlt => _
  obtain ⟨I', hI'⟩ := hJX.indep.ssubset_indep_of_card_lt hI hlt
  have := hJX.eq_of_subset_indep hI'.1 hI'.2.1.Subset (hI'.2.2.trans (union_subset hJX.subset hIX))
  subst this
  exact hI'.2.1.Ne rfl

end Finite

end Matroid

