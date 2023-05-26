import Matroid.Connectivity
import Matroid.Simple
import Matroid.Maps.Equiv

open Classical

open BigOperators

-- noncomputable theory
open Matroid Set Subtype

variable {α : Type _}

/- a `matroid_in α` is a matroid defined on some subset `E` of `α`. Implemented as a `matroid` on
  which the nonelements of `E` are all loops.

  The main motivation for this is to have a way of talking about minors that avoids type equality.
  Pseudominors give one way of doing this, while staying in `matroid E`, but they are a bit ugly
  with duality. The advantage of `matroid_in` is that, if `M : matroid_in α`, then `M﹡` and
  `M ⟋ C ⟍ D` are both `matroid_in α`, and we can say things like `(M / C \ D)﹡ = M﹡ ⟍ C ⟋ D`
  meaningfully and without type equality.

  The disadvantages are having keep track of a ground set, and API duplication.
  -/
/-- A matroid on some subset `E` of `α`. Implemented as a `matroid` in which the elements
outside `E` are all loops. -/
@[ext]
structure MatroidIn (α : Type _) where
  ground : Set α
  carrier : Matroid α
  support : groundᶜ ⊆ carrier.cl ∅

namespace MatroidIn

/-- The coercion of a `matroid_in α` to a `matroid α`. The coerced matroid has only loops
  outside the ground set; most `matroid_in` properties are defined using this coercion, because
  the definitional properties are convenient for going between `matroid_in` and `matroid` APIs. -/
instance {α : Type _} : Coe (MatroidIn α) (Matroid α) :=
  ⟨fun M => M.carrier⟩

@[simp]
theorem carrier_eq_coe {M : MatroidIn α} : M.carrier = (M : Matroid α) :=
  rfl

/-- The ground set of a `matroid_in`. This is some `set` of the ambient type. -/
def e (M : MatroidIn α) :=
  M.ground

@[simp]
theorem ground_eq_e (M : MatroidIn α) : M.ground = M.e :=
  rfl

/-- A `matroid_in` is `finite_rk` if its ground set has a finite base -/
class FiniteRk (M : MatroidIn α) : Prop where
  Fin : FiniteRk (M : Matroid α)

instance FiniteRk.to_coe {M : MatroidIn α} [FiniteRk M] : (M : Matroid α).FiniteRk :=
  ‹FiniteRk M›.Fin

section Equivalence

variable {X X₁ X₂ E : Set α}

/-- A `matroid_in` gives a matroid on a subtype -/
def toMatroid (M : MatroidIn α) : Matroid M.e :=
  (M : Matroid α).Preimage (Function.Embedding.subtype M.e)

def toMatroidOfGroundEq (M : MatroidIn α) (hX : M.e = X) : Matroid X :=
  M.toMatroid.congr (Equiv.setCongr hX)

/-- A `matroid` on a subtype gives a `matroid_in` -/
def toMatroidIn {E : Set α} (M : Matroid E) : MatroidIn α :=
  ⟨E, M.image (Function.Embedding.subtype E),
    by
    intro e he
    simp_rw [← Matroid.loop_iff_mem_cl_empty, Matroid.loop_iff_dep, image.indep_iff,
      Function.Embedding.coe_subtype, not_exists, not_and, coe_injective.image_eq_singleton_iff]
    rintro I hI ⟨⟨x, hx⟩, rfl, rfl⟩
    exact he hx⟩

/-- A `matroid_in α` with ground set `E` is the same thing as a `matroid E`-/
def equivSubtype : { M : MatroidIn α // M.e = E } ≃ Matroid E
    where
  toFun M := toMatroidOfGroundEq (M : MatroidIn α) M.2
  invFun M := ⟨toMatroidIn M, rfl⟩
  left_inv := by
    rintro ⟨M, rfl⟩
    simp only [to_matroid_of_ground_eq, to_matroid_in, to_matroid, coe_mk, congr_eq_preimage,
      preimage.trans]
    refine' MatroidIn.ext _ _ rfl _
    convert(M : Matroid α).image_preimage_eq_of_forall_subset_range (Function.Embedding.subtype M.E)
        fun I hI => _
    simp only [Function.Embedding.coe_subtype, range_coe_subtype, setOf]
    rw [← compl_compl M.E]
    exact fun e he heM => Matroid.Indep.nonloop_of_mem hI he (M.support heM)
  right_inv := by
    rintro M
    simp only [coe_mk, to_matroid_of_ground_eq, to_matroid_in, congr_eq_preimage, to_matroid, ←
      carrier_eq_coe, preimage.trans]
    convert M.preimage_image _

theorem equivSubtype_apply {E : Set α} {M : { M : MatroidIn α // M.e = E }} :
    equivSubtype M = (M : Matroid α).Preimage (Function.Embedding.subtype E) :=
  by
  simp [equiv_subtype, to_matroid_of_ground_eq, to_matroid]
  congr

theorem equivSubtype_apply_symm_coe_coe {E : Set α} (M : Matroid E) :
    ((equivSubtype.symm M : MatroidIn α) : Matroid α) = M.image (Function.Embedding.subtype E) := by
  simp [equiv_subtype, to_matroid_in, ← carrier_eq_coe]

@[simp]
theorem equivSubtype.symm_ground_eq (M : Matroid E) : (equivSubtype.symm M : MatroidIn α).e = E :=
  rfl

def Equiv.setSubtype {α : Type _} (X : Set α) : { S : Set α // S ⊆ X } ≃ Set X
    where
  toFun S := coe ⁻¹' (S : Set α)
  invFun Y := ⟨coe '' Y, by simp⟩
  right_inv S := by simp [preimage_image_eq _ coe_injective]
  left_inv S := by
    obtain ⟨S, h⟩ := S
    simpa

@[simp]
theorem Equiv.setSubtype_apply (S) : Equiv.setSubtype X S = coe ⁻¹' (S : Set α) :=
  rfl

@[simp]
theorem Equiv.setSubtype_apply_symm_coe (S) : ((Equiv.setSubtype X).symm S : Set α) = coe '' S :=
  rfl

theorem eq_image_symm_image_equivSubtype (M : MatroidIn α) :
    (equivSubtype.symm (equivSubtype ⟨M, rfl⟩) : MatroidIn α) = M := by
  simp_rw [Equiv.symm_apply_apply, coe_mk]

section Transfer

/-- Transfer a `matroid` property of sets to a `matroid_in` property. -/
def TransferSetProp (P : ∀ ⦃γ : Type _⦄ (M : Matroid γ), Set γ → Prop) :
    ∀ M : MatroidIn α, Set α → Prop := fun M X =>
  ∃ h : X ⊆ M.e, P M.toMatroid (Equiv.setSubtype M.e ⟨X, h⟩)

/-- Transfer a `matroid` property of pairs of sets to a `matroid_in` property. -/
def TransferSetProp₂ (P : ∀ ⦃γ : Type _⦄ (M : Matroid γ), Set γ → Set γ → Prop) :
    ∀ M : MatroidIn α, Set α → Set α → Prop := fun M X₁ X₂ =>
  ∃ (h₁ : X₁ ⊆ M.e)(h₂ : X₂ ⊆ M.e),
    P M.toMatroid (Equiv.setSubtype M.e ⟨X₁, h₁⟩) (Equiv.setSubtype M.e ⟨X₂, h₂⟩)

theorem transferSetProp_iff {P} {M : MatroidIn α} :
    TransferSetProp P M X ↔ P (equivSubtype ⟨M, rfl⟩) (coe ⁻¹' X) ∧ X ⊆ M.e := by
  simp [transfer_set_prop, equiv_subtype_apply, to_matroid, and_comm']

theorem transferSetProp₂_iff {P} {M : MatroidIn α} :
    TransferSetProp₂ P M X₁ X₂ ↔
      P (equivSubtype ⟨M, rfl⟩) (coe ⁻¹' X₁) (coe ⁻¹' X₂) ∧ X₁ ⊆ M.e ∧ X₂ ⊆ M.e :=
  by simp [transfer_set_prop₂, equiv_subtype_apply, to_matroid, and_comm', ← and_assoc']

@[simp]
theorem transferSetProp_iff_symm {P} {M : Matroid E} {X : Set E} :
    (TransferSetProp P) (equivSubtype.symm M : MatroidIn α) (coe '' X) ↔ P M X :=
  by
  rw [← equiv_subtype.apply_symm_apply M]
  simpa [transfer_set_prop_iff]

@[simp]
theorem transferSetProp_coe_iff {P} {M : MatroidIn α} {X : Set M.e} :
    (TransferSetProp P) M (coe '' X) ↔ P (equivSubtype ⟨M, rfl⟩) X := by
  simp [transfer_set_prop_iff]

@[simp]
theorem transferSetProp₂_iff_symm {P} {E : Set α} {M : Matroid E} {X₁ X₂ : Set E} :
    (TransferSetProp₂ P) (equivSubtype.symm M : MatroidIn α) (coe '' X₁) (coe '' X₂) ↔ P M X₁ X₂ :=
  by
  rw [← equiv_subtype.apply_symm_apply M]
  simpa [transfer_set_prop₂_iff]

@[simp]
theorem transferSetProp₂_coe_iff {P} {M : MatroidIn α} {X₁ X₂ : Set M.e} :
    (TransferSetProp₂ P) M (coe '' X₁) (coe '' X₂) ↔ P (equivSubtype ⟨M, rfl⟩) X₁ X₂ := by
  simp [transfer_set_prop₂_iff]

theorem TransferSetProp.subset_ground {P} {M : MatroidIn α} (hX : TransferSetProp P M X) :
    X ⊆ M.e :=
  Exists.elim hX fun h _ => h

theorem TransferSetProp.inter_ground {P} {M : MatroidIn α} (hX : TransferSetProp P M X) :
    X ∩ M.e = X :=
  inter_eq_self_of_subset_left hX.subset_ground

theorem TransferSetProp.exists_eq_coe {P} {M : MatroidIn α} (hX : TransferSetProp P M X) :
    ∃ X₀ : Set M.e, P (equivSubtype ⟨M, rfl⟩) X₀ ∧ X = coe '' X₀ :=
  by
  simp_rw [transfer_set_prop_iff, ← @range_coe _ M.E, subset_range_iff_exists_image_eq] at hX
  obtain ⟨hX₀, X₀, rfl⟩ := hX
  exact ⟨_, by simpa using hX₀, rfl⟩

theorem TransferSetProp₂.exists_eq_coe {P} {M : MatroidIn α} {X₁ X₂ : Set α}
    (hX : TransferSetProp₂ P M X₁ X₂) :
    ∃ X₁' X₂' : Set M.e, P (equivSubtype ⟨M, rfl⟩) X₁' X₂' ∧ X₁ = coe '' X₁' ∧ X₂ = coe '' X₂' :=
  by
  simp_rw [transfer_set_prop₂_iff, ← @range_coe _ M.E, subset_range_iff_exists_image_eq] at hX
  obtain ⟨hX', ⟨X₁', rfl⟩, ⟨X₁', rfl⟩⟩ := hX
  exact ⟨_, _, by simpa using hX', rfl, rfl⟩

@[simp]
theorem transferSetProp_forall_iff {P} {M : MatroidIn α} {Q : Set α → Prop} :
    (∀ X, TransferSetProp P M X → Q X) ↔
      ∀ Y : Set M.e, P (equivSubtype ⟨M, rfl⟩) Y → Q (coe '' Y) :=
  by
  refine' ⟨fun h Y hPY => h _ (transfer_set_prop_coe_iff.mpr hPY), fun h X hPX => _⟩
  obtain ⟨Y, hY, rfl⟩ := hPX.exists_eq_coe
  exact h _ hY

@[simp]
theorem transferSetProp₂_forall_iff {P} {M : MatroidIn α} {Q : Set α → Set α → Prop} :
    (∀ X₁ X₂, TransferSetProp₂ P M X₁ X₂ → Q X₁ X₂) ↔
      ∀ Y₁ Y₂ : Set M.e, P (equivSubtype ⟨M, rfl⟩) Y₁ Y₂ → Q (coe '' Y₁) (coe '' Y₂) :=
  by
  refine' ⟨fun h Y₁ Y₂ hP => h _ _ (transfer_set_prop₂_coe_iff.mpr hP), fun h X₁ X₂ hP => _⟩
  obtain ⟨Y₁, Y₂, hY, rfl, rfl⟩ := hP.exists_eq_coe
  exact h _ _ hY

@[simp]
theorem transferSetProp_exists_iff {P} {M : MatroidIn α} {Q : Set α → Prop} :
    (∃ X, TransferSetProp P M X ∧ Q X) ↔
      ∃ Y : Set M.e, P (equivSubtype ⟨M, rfl⟩) Y ∧ Q (coe '' Y) :=
  by
  constructor
  · rintro ⟨X, hPX, hQX⟩
    obtain ⟨Y, hY, rfl⟩ := hPX.exists_eq_coe
    refine' ⟨Y, hY, hQX⟩
  rintro ⟨Y, hY⟩
  exact ⟨coe '' Y, by rwa [transfer_set_prop_coe_iff]⟩

theorem TransferSetProp₂.subset_ground_left {P} {M : MatroidIn α} {X₁ X₂ : Set α}
    (hX : TransferSetProp₂ P M X₁ X₂) : X₁ ⊆ M.e :=
  let ⟨h, _, _⟩ := hX
  h

theorem TransferSetProp₂.subset_ground_right {P} {M : MatroidIn α} {X₁ X₂ : Set α}
    (hX : TransferSetProp₂ P M X₁ X₂) : X₂ ⊆ M.e :=
  let ⟨_, h, _⟩ := hX
  h

theorem TransferSetProp₂.inter_ground_left {P} {M : MatroidIn α} {X₁ X₂ : Set α}
    (hX : TransferSetProp₂ P M X₁ X₂) : X₁ ∩ M.e = X₁ :=
  inter_eq_self_of_subset_left hX.subset_ground_left

theorem TransferSetProp₂.inter_ground_right {P} {M : MatroidIn α} {X₁ X₂ : Set α}
    (hX : TransferSetProp₂ P M X₁ X₂) : X₂ ∩ M.e = X₂ :=
  inter_eq_self_of_subset_left hX.subset_ground_right

/-- The type of sets in `α` satisfying `transfer_set_prop P` corresponds to the type of sets in
  `M.E` satisfying `P` -/
def transferSetPropEquiv (P) (M : MatroidIn α) :
    { X : Set α // TransferSetProp P M X } ≃ { Y : Set M.e // P (equivSubtype ⟨M, rfl⟩) Y }
    where
  toFun X := ⟨coe ⁻¹' (X : Set α), (transferSetProp_iff.mp X.2).1⟩
  invFun Y := ⟨coe '' (Y : Set M.e), by simpa using Y.2⟩
  left_inv := by
    rintro ⟨X, hX⟩
    simp [hX.subset_ground]
  right_inv := by
    rintro ⟨Y, hY⟩
    simp

@[simp]
theorem transferSetPropEquiv_apply {P} (M : MatroidIn α) {X : Set α} (hX : TransferSetProp P M X) :
    (transferSetPropEquiv P M ⟨X, hX⟩ : Set M.e) = coe ⁻¹' X :=
  rfl

@[simp]
theorem transferSetPropEquiv_apply_symm {P : ∀ ⦃γ : Type _⦄ (M : Matroid γ), Set γ → Prop}
    (M : MatroidIn α) {Y : Set M.e} (hY : P (equivSubtype ⟨M, rfl⟩) Y) :
    ((transferSetPropEquiv P M).symm ⟨Y, hY⟩ : Set α) = coe '' Y :=
  rfl

end Transfer

end Equivalence

variable {M : MatroidIn α} {X Y I J C B F H K : Set α} {e f : α} {k : ℕ}

section Basic

theorem loop_coe_of_not_mem_ground (h : e ∉ M.e) : (M : Matroid α).Loop e :=
  M.support (mem_compl h)

theorem mem_ground_of_nonloop_coe (h : (M : Matroid α).Nonloop e) : e ∈ M.e :=
  by_contra fun he => h (M.support he)

theorem compl_ground_subset_loops_coe (M : MatroidIn α) : M.eᶜ ⊆ (M : Matroid α).cl ∅ :=
  M.support

theorem subset_ground_of_disjoint_loops_coe (hX : Disjoint X ((M : Matroid α).cl ∅)) : X ⊆ M.e :=
  hX.subset_compl_right.trans (compl_subset_comm.mp M.support)

theorem subset_loops_coe_of_disjoint_ground (hX : Disjoint X M.e) : X ⊆ (M : Matroid α).cl ∅ :=
  hX.subset_compl_right.trans (compl_ground_subset_loops_coe _)

instance coe_finiteRk_of_finite {M : MatroidIn α} [Finite M.e] : (M : Matroid α).FiniteRk :=
  ⟨by
    obtain ⟨B, hB⟩ := (M : Matroid α).exists_base
    exact
      ⟨B, hB, (to_finite M.E).Subset (subset_ground_of_disjoint_loops_coe hB.indep.disjoint_loops)⟩⟩

/-! Independence -/


/-- A `base` is a maximal independent set -/
def Base (M : MatroidIn α) (B : Set α) : Prop :=
  (M : Matroid α).base B

/-- An `indep`endent set is a subset of a base -/
def Indep (M : MatroidIn α) (I : Set α) : Prop :=
  (M : Matroid α).indep I

/-- A `basis` for `X` is a maximal independent subset of `X` -/
def Basis (M : MatroidIn α) (I X : Set α) : Prop :=
  (M : Matroid α).Basis I X ∧ X ⊆ M.e

theorem Indep.subset_ground (hI : M.indep I) : I ⊆ M.e :=
  subset_ground_of_disjoint_loops_coe (Matroid.Indep.disjoint_loops hI)

theorem base_iff_coe : M.base B ↔ (M : Matroid α).base B :=
  Iff.rfl

theorem Base.to_coe (hB : M.base B) : (M : Matroid α).base B :=
  hB

theorem exists_base (M : MatroidIn α) : ∃ B, M.base B :=
  Matroid.exists_base M

theorem Base.indep (hB : M.base B) : M.indep B :=
  Matroid.Base.indep hB

theorem Base.subset_ground (hB : M.base B) : B ⊆ M.e :=
  hB.indep.subset_ground

theorem Base.finite [FiniteRk M] (hB : M.base B) : B.Finite :=
  hB.to_coe.Finite

theorem Base.insert_dep (hB : M.base B) (he : e ∉ B) : ¬M.indep (insert e B) :=
  Matroid.Base.insert_dep hB he

theorem indep_iff_coe : M.indep I ↔ (M : Matroid α).indep I :=
  Iff.rfl

theorem Indep.to_coe (hI : M.indep I) : (M : Matroid α).indep I :=
  hI

theorem indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B :=
  Iff.rfl

theorem Indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B :=
  hI

theorem Indep.finite [FiniteRk M] (hI : M.indep I) : I.Finite :=
  Exists.elim (indep_iff_subset_base.mp hI) fun B hB => hB.1.Finite.Subset hB.2

theorem Indep.subset (hI : M.indep I) (hX : X ⊆ I) : M.indep X :=
  Matroid.Indep.subset hI hX

theorem Indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) (hX : X ⊆ M.e) :
    ∃ J, I ⊆ J ∧ M.Basis J X :=
  by
  obtain ⟨J, hJ, hIJ⟩ := Matroid.Indep.subset_basis_of_subset hI hIX
  exact ⟨J, hIJ, ⟨hJ, hX⟩⟩

theorem Indep.basis_self (hI : M.indep I) : M.Basis I I :=
  ⟨hI.to_coe.basis_self, hI.subset_ground⟩

theorem Basis.to_coe (h : M.Basis I X) : (M : Matroid α).Basis I X :=
  h.1

theorem Basis.indep (hIX : M.Basis I X) : M.indep I :=
  Matroid.Basis.indep hIX.1

theorem Basis.subset (hIX : M.Basis I X) : I ⊆ X :=
  Matroid.Basis.subset hIX.1

theorem Basis.subset_ground (hIX : M.Basis I X) : X ⊆ M.e :=
  hIX.2

theorem exists_basis (M : MatroidIn α) (hX : X ⊆ M.e) : ∃ I, M.Basis I X :=
  by
  obtain ⟨I, hI⟩ := Matroid.exists_basis (M : Matroid α) X
  exact ⟨I, hI, hX⟩

theorem base_iff_basis_ground : M.base B ↔ M.Basis B M.e :=
  by
  rw [base, Basis, iff_true_intro subset.rfl, and_true_iff, Matroid.basis_iff,
    Matroid.base_iff_maximal_indep, and_congr_right_iff]
  exact fun hi =>
    ⟨fun h => ⟨indep.subset_ground hi, fun J hJ hBJ _ => h _ hJ hBJ⟩, fun h I hI hBI =>
      h.2 _ hI hBI (indep.subset_ground hI)⟩

/-- A set is `r_fin` in `M` if it has a finite basis -/
def RFin (M : MatroidIn α) (X : Set α) :=
  (M : Matroid α).RFin X ∧ X ⊆ M.e

theorem RFin.to_coe (h : M.RFin X) : (M : Matroid α).RFin X :=
  h.1

theorem RFin.subset_ground (h : M.RFin X) : X ⊆ M.e :=
  h.2

theorem to_rFin [FiniteRk M] (h : X ⊆ M.e) : M.RFin X :=
  ⟨Matroid.to_rFin (M : Matroid α) X, h⟩

theorem Basis.rFin_iff_finite (hI : M.Basis I X) : M.RFin X ↔ I.Finite := by
  rw [r_fin, hI.to_coe.r_fin_iff_finite, and_iff_left hI.subset_ground]

theorem Indep.rFin_iff_finite (hI : M.indep I) : M.RFin I ↔ I.Finite :=
  hI.basis_self.rFin_iff_finite

theorem RFin.subset (h : M.RFin X) (hY : Y ⊆ X) : M.RFin Y :=
  ⟨h.to_coe.Subset hY, hY.trans h.subset_ground⟩

theorem rFin_of_finite (hX : X ⊆ M.e) (hfin : X.Finite) : M.RFin X :=
  ⟨Matroid.rFin_of_finite M hfin, hX⟩

/-- Needs a `matroid` version-/
theorem rFin_singleton (he : e ∈ M.e) : M.RFin {e} :=
  rFin_of_finite (singleton_subset_iff.mpr he) (finite_singleton e)

@[simp]
theorem rFin_empty (M : MatroidIn α) : M.RFin ∅ :=
  rFin_of_finite (empty_subset _) finite_empty

theorem RFin.union (hX : M.RFin X) (hY : M.RFin Y) : M.RFin (X ∪ Y) :=
  ⟨hX.to_coe.union hY.to_coe, union_subset hX.subset_ground hY.subset_ground⟩

/-- Needs a `matroid` version-/
theorem rFin_union_iff : M.RFin (X ∪ Y) ↔ M.RFin X ∧ M.RFin Y :=
  ⟨fun h => ⟨h.Subset (subset_union_left X Y), h.Subset (subset_union_right X Y)⟩, fun h =>
    h.1.union h.2⟩

@[simp]
theorem equivSubtype.indep_iff {E : Set α} {I : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).indep I ↔ (M : MatroidIn α).indep (coe '' I) := by
  simp [equiv_subtype_apply, indep_iff_coe]

theorem equivSubtype.symm_indep_iff_exists {E I : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).indep I ↔ ∃ I₀, M.indep I₀ ∧ coe '' I₀ = I :=
  by
  rw [indep_iff_coe, equiv_subtype_apply_symm_coe_coe]
  simp

@[simp]
theorem equivSubtype.symm_indep_iff {E I : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).indep I ↔ M.indep (coe ⁻¹' I) ∧ I ⊆ E :=
  by
  rw [← Equiv.apply_symm_apply equiv_subtype M, equiv_subtype.indep_iff, Equiv.apply_symm_apply,
    image_preimage_eq_inter_range, range_coe]
  refine' ⟨fun h => ⟨h.Subset (inter_subset_left _ _), h.subset_ground⟩, _⟩
  rintro ⟨hi, hIE⟩
  rwa [inter_eq_self_of_subset_left hIE] at hi

theorem indep_eq_transferSetProp (M : MatroidIn α) :
    M.indep = TransferSetProp (fun _ => Matroid.Indep) M :=
  by
  ext X
  simp only [transfer_set_prop_iff, equiv_subtype.indep_iff, coe_mk, image_preimage_coe]
  refine'
    ⟨fun h => ⟨by rwa [inter_eq_self_of_subset_left h.subset_ground], h.subset_ground⟩, fun h => _⟩
  rw [← inter_eq_self_of_subset_left h.2]
  exact h.1

@[simp]
theorem equivSubtype.basis_iff {E : Set α} {I X : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).Basis I X ↔ (M : MatroidIn α).Basis (coe '' I) (coe '' X) :=
  by
  obtain ⟨M, rfl⟩ := M
  simp [equiv_subtype_apply, Basis]

@[simp]
theorem equivSubtype.symm_basis_iff {E I X : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Basis I X ↔
      M.Basis (coe ⁻¹' I) (coe ⁻¹' X) ∧ I ⊆ E ∧ X ⊆ E :=
  by
  rw [← Equiv.apply_symm_apply equiv_subtype M]
  simp_rw [equiv_subtype.basis_iff, Equiv.apply_symm_apply, image_preimage_coe]
  refine' ⟨fun h => _, _⟩
  · have hXE : X ⊆ E := h.subset_ground
    rw [inter_eq_self_of_subset_left hXE, inter_eq_self_of_subset_left (h.subset.trans hXE)]
    exact ⟨h, h.subset.trans hXE, hXE⟩
  rintro ⟨h, hIE, hXE⟩
  rwa [inter_eq_self_of_subset_left hIE, inter_eq_self_of_subset_left hXE] at h

theorem equivSubtype.symm_basis_iff_exists {E I X : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Basis I X ↔
      ∃ I₀ X₀, M.Basis I₀ X₀ ∧ I = coe '' I₀ ∧ X = coe '' X₀ :=
  by
  rw [equiv_subtype.symm_basis_iff]
  refine' ⟨fun h => ⟨_, _, h.1, _, _⟩, _⟩
  · rw [eq_comm, image_preimage_eq_iff, range_coe]
    exact h.2.1
  · rw [eq_comm, image_preimage_eq_iff, range_coe]
    exact h.2.2
  rintro ⟨I, X, h, rfl, rfl⟩
  simp_rw [← @range_coe _ E, preimage_image_eq _ coe_injective,
    and_iff_left (image_subset_range _ _), iff_true_intro h]

@[simp]
theorem equivSubtype.base_iff {E : Set α} {B : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).base B ↔ (M : MatroidIn α).base (coe '' B) :=
  by
  obtain ⟨M, rfl⟩ := M
  simp only [equiv_subtype_apply, base_iff_coe, coe_coe, coe_mk, preimage.base_iff,
    Function.Embedding.coe_subtype, range_coe_subtype, setOf, base_iff_basis_ground, Basis,
    iff_true_intro subset.rfl, and_true_iff]

theorem base_eq_transferSetProp (M : MatroidIn α) :
    M.base = TransferSetProp (fun _ => Matroid.Base) M :=
  by
  ext X
  simp only [transfer_set_prop_iff, equiv_subtype.base_iff, coe_mk, image_preimage_coe]
  refine'
    ⟨fun h => ⟨by rwa [inter_eq_self_of_subset_left h.subset_ground], h.subset_ground⟩, fun h => _⟩
  rw [← inter_eq_self_of_subset_left h.2]
  exact h.1

theorem equivSubtype.symm_base_iff_exists {E B : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).base B ↔ ∃ B₀, M.base B₀ ∧ B = coe '' B₀ :=
  by
  simp_rw [base_iff_coe, equiv_subtype_apply_symm_coe_coe, image.base_iff]
  convert Iff.rfl

@[simp]
theorem equivSubtype.symm_base_iff {E B : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).base B ↔ M.base (coe ⁻¹' B) ∧ B ⊆ E :=
  by
  rw [equiv_subtype.symm_base_iff_exists]
  refine' ⟨_, fun h => ⟨_, h.1, _⟩⟩
  · rintro ⟨B, hB, rfl⟩
    simp_rw [preimage_image_eq _ coe_injective, ← @range_coe _ E,
      and_iff_left (image_subset_range _ _), iff_true_intro hB]
  rw [image_preimage_eq_inter_range, range_coe, inter_eq_self_of_subset_left h.2]

@[simp]
theorem equivSubtype.rFin_iff {E : Set α} {X : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).RFin X ↔ (M : MatroidIn α).RFin (coe '' X) :=
  by
  obtain ⟨I, hI⟩ := (equiv_subtype M).exists_basis X
  rw [hI.r_fin_iff_finite, ((equiv_subtype.basis_iff _).mp hI).rFin_iff_finite,
    finite_image_iff (coe_injective.inj_on _)]

@[simp]
theorem equivSubtype.symm_rFin_iff {E X : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).RFin X ↔ M.RFin (coe ⁻¹' X) ∧ X ⊆ E :=
  by
  rw [← Equiv.apply_symm_apply equiv_subtype M]
  simp_rw [equiv_subtype.r_fin_iff, Equiv.apply_symm_apply, image_preimage_coe]
  refine' ⟨fun h => _, _⟩
  · have hXE : X ⊆ E := h.subset_ground
    exact ⟨by rwa [inter_eq_self_of_subset_left hXE], hXE⟩
  rintro ⟨h₁, h₂⟩
  rwa [inter_eq_self_of_subset_left h₂] at h₁

theorem equivSubtype.symm_rFin_iff_exists {E X : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).RFin X ↔ ∃ X₀, M.RFin X₀ ∧ X = coe '' X₀ :=
  by
  rw [equiv_subtype.symm_r_fin_iff]
  refine'
    ⟨fun h =>
      ⟨_, h.1, by
        rw [eq_comm, image_preimage_eq_iff, range_coe]
        exact h.2⟩,
      _⟩
  rintro ⟨F₀, hF₀, rfl⟩
  simp_rw [preimage_image_eq _ coe_injective, ← @range_coe _ E]
  exact ⟨hF₀, image_subset_range _ _⟩

theorem rFin_eq_transferSetProp (M : MatroidIn α) :
    M.RFin = TransferSetProp (fun _ => Matroid.RFin) M :=
  by
  ext X
  simp_rw [transfer_set_prop_iff, equiv_subtype.r_fin_iff, coe_mk, image_preimage_coe, r_fin,
    and_iff_left (inter_subset_right _ _), and_congr_left_iff]
  intro h
  rw [inter_eq_self_of_subset_left h]

/-! Circuits -/


/-- A `circuit` is a minimal dependent set. -/
def Circuit (M : MatroidIn α) (C : Set α) :=
  (M : Matroid α).Circuit C ∧ C ⊆ M.e

theorem Circuit.subset_ground (hC : M.Circuit C) : C ⊆ M.e :=
  hC.2

theorem Circuit.to_coe (hC : M.Circuit C) : (M : Matroid α).Circuit C :=
  hC.1

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊂ » C) -/
theorem circuit_iff : M.Circuit C ↔ (¬M.indep C ∧ ∀ (I) (_ : I ⊂ C), M.indep I) ∧ C ⊆ M.e :=
  by
  rw [circuit, Matroid.circuit_iff_forall_sSubset]
  rfl

theorem circuit_iff_coe : M.Circuit C ↔ (M : Matroid α).Circuit C ∧ C ⊆ M.e :=
  Iff.rfl

theorem circuit_coe_iff : (M : Matroid α).Circuit C ↔ M.Circuit C ∨ ∃ e ∈ M.eᶜ, C = {e} :=
  by
  rw [circuit]
  refine' (em (C ⊆ M.E)).elim (fun hC => _) fun hC => _
  · rw [or_iff_left, iff_true_intro hC, and_true_iff]
    rintro ⟨e, hec, rfl⟩
    exact hec (hC (mem_singleton e))
  rw [or_iff_right (hC ∘ And.right)]
  obtain ⟨e, heC, heM⟩ := not_subset_iff_exists_mem_not_mem.mp hC
  have hl := (loop_coe_of_not_mem_ground heM).Circuit
  refine'
    ⟨fun h => ⟨e, heM, (hl.eq_of_subset_circuit h (singleton_subset_iff.mpr heC)).symm⟩, fun h => _⟩
  obtain ⟨f, hf, rfl⟩ := h
  rwa [← mem_singleton_iff.mp heC]

theorem circuit_iff_mem_minimals :
    M.Circuit C ↔ C ∈ minimals (· ⊆ ·) { X | ¬M.indep X ∧ X ⊆ M.e } :=
  ⟨fun h => ⟨⟨h.1.1, h.2⟩, fun D hD hDC => h.1.2 hD.1 hDC⟩, fun h =>
    ⟨⟨h.1.1, fun D hD hDC => h.2 ⟨hD, hDC.trans h.1.2⟩ hDC⟩, h.1.2⟩⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (C «expr ⊆ » I) -/
theorem indep_iff_forall_subset_not_circuit :
    M.indep I ↔ (∀ (C) (_ : C ⊆ I), ¬M.Circuit C) ∧ I ⊆ M.e :=
  by
  simp_rw [indep_iff_coe, Matroid.indep_iff_forall_subset_not_circuit, MatroidIn.Circuit, not_and]
  refine'
    ⟨fun h => ⟨fun C hCI hC => (h C hCI hC).elim, fun e heI => by_contra fun heE => _⟩,
      fun h C hCI hC => _⟩
  · have hl := Matroid.Loop.circuit (loop_coe_of_not_mem_ground heE)
    exact h {e} (singleton_subset_iff.mpr heI) hl
  exact h.1 C hCI hC (hCI.trans h.2)

@[simp]
theorem equivSubtype.circuit_iff {E : Set α} {C : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).Circuit C ↔ (M : MatroidIn α).Circuit (coe '' C) :=
  by
  obtain ⟨M, rfl⟩ := M
  simp_rw [circuit, equiv_subtype_apply, preimage.circuit_iff, coe_coe,
    Function.Embedding.coe_subtype, iff_self_and, coe_mk, ← @range_coe _ M.E,
    iff_true_intro (image_subset_range _ _), imp_true_iff]

@[simp]
theorem equivSubtype.symm_circuit_iff {E C : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Circuit C ↔ M.Circuit (coe ⁻¹' C) ∧ C ⊆ E :=
  by
  rw [← Equiv.apply_symm_apply equiv_subtype M, equiv_subtype.circuit_iff, Equiv.apply_symm_apply,
    image_preimage_coe]
  refine' ⟨fun h => _, _⟩
  · have hCE : C ⊆ E := h.subset_ground
    exact ⟨by rwa [inter_eq_self_of_subset_left hCE], hCE⟩
  rintro ⟨h₁, h₂⟩
  rwa [inter_eq_self_of_subset_left h₂] at h₁

theorem equivSubtype.symm_circuit_iff_exists {E C : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Circuit C ↔ ∃ C₀, M.Circuit C₀ ∧ C = coe '' C₀ :=
  by
  rw [equiv_subtype.symm_circuit_iff]
  refine'
    ⟨fun h =>
      ⟨_, h.1, by
        rw [eq_comm, image_preimage_eq_iff, range_coe]
        exact h.2⟩,
      _⟩
  rintro ⟨F₀, hF₀, rfl⟩
  simp_rw [preimage_image_eq _ coe_injective, ← @range_coe _ E]
  exact ⟨hF₀, image_subset_range _ _⟩

theorem circuit_eq_transferSetProp (M : MatroidIn α) :
    M.Circuit = TransferSetProp (fun _ => Matroid.Circuit) M :=
  by
  ext C
  simp only [transfer_set_prop_iff, equiv_subtype.circuit_iff, coe_mk, image_preimage_coe]
  refine' ⟨fun h => ⟨_, h.subset_ground⟩, _⟩
  · rwa [inter_eq_self_of_subset_left h.subset_ground]
  rintro ⟨hC, hE⟩
  rwa [inter_eq_self_of_subset_left hE] at hC

/-- The `girth` of `M` is the length of its smallest finite circuit, or zero if none exists -/
noncomputable def girth (M : MatroidIn α) :=
  (equivSubtype ⟨M, rfl⟩).girth

theorem girth_eq_zero_iff : M.girth = 0 ↔ ∀ C, M.Circuit C → C.Infinite :=
  by
  simp_rw [girth, Matroid.girth_eq_zero_iff, equiv_subtype.circuit_iff, coe_mk]
  refine' ⟨fun h C hC hCfin => h (coe ⁻¹' C) _ _, fun h C hC hCfin => h _ hC (hCfin.image _)⟩
  · convert hC
    rw [image_preimage_eq_iff, range_coe]
    exact hC.subset_ground
  exact hCfin.preimage (coe_injective.inj_on _)

theorem girth_le_iff {k : ℕ} (h : M.girth ≠ 0) :
    M.girth ≤ k ↔ ∃ C, M.Circuit C ∧ C.Finite ∧ C.ncard ≤ k :=
  by
  simp_rw [girth, Matroid.girth_le_iff h, equiv_subtype.circuit_iff, coe_mk]
  constructor
  · rintro ⟨C, hC, hCfin, hCcard⟩
    refine' ⟨_, hC, hCfin.image coe, _⟩
    rwa [ncard_image_of_injective _ coe_injective]
  rintro ⟨C, hC, hCfin, hCcard⟩
  refine' ⟨coe ⁻¹' C, _, hCfin.preimage (coe_injective.inj_on _), _⟩
  · convert hC
    rw [image_preimage_eq_iff, range_coe]
    exact hC.subset_ground
  rwa [ncard_preimage_of_injective_subset_range coe_injective]
  rw [range_coe]
  exact hC.subset_ground

theorem le_girth_iff {k : ℕ} (h : M.girth ≠ 0) :
    k ≤ M.girth ↔ ∀ C, M.Circuit C → C.Finite → k ≤ C.ncard :=
  by
  simp_rw [girth, Matroid.le_girth_iff h, equiv_subtype.circuit_iff, coe_mk]
  refine' ⟨fun h' C hC hCfin => _, fun h' C hC hCfin => _⟩
  · convert h' (coe ⁻¹' C) _ _ using 1
    · rw [ncard_preimage_of_injective_subset_range coe_injective]
      rw [range_coe]
      exact hC.subset_ground
    · convert hC
      rw [image_preimage_eq_iff, range_coe]
      exact hC.subset_ground
    exact hCfin.preimage (coe_injective.inj_on _)
  convert h' _ hC (hCfin.image coe) using 1
  rw [ncard_image_of_injective _ coe_injective]

-- ### Closure and flats
variable {F₁ F₂ : Set α}

/-- A flat is a maximal set having a given basis -/
def Flat (M : MatroidIn α) (F : Set α) :=
  (M : Matroid α).Flat (F ∪ M.eᶜ) ∧ F ⊆ M.e

/-- The closure of a set is the intersection of the flats containing it -/
def cl (M : MatroidIn α) (X : Set α) :=
  (M : Matroid α).cl X ∩ M.e

def Hyperplane (M : MatroidIn α) (H : Set α) :=
  (M : Matroid α).Hyperplane (H ∪ M.eᶜ) ∧ H ⊆ M.e

theorem cl_eq_coe_cl_inter (M : MatroidIn α) (X : Set α) : M.cl X = (M : Matroid α).cl X ∩ M.e :=
  rfl

theorem cl_coe_eq (M : MatroidIn α) (X : Set α) : (M : Matroid α).cl X = M.cl X ∪ M.eᶜ :=
  by
  rw [cl, union_distrib_right, union_compl_self, inter_univ, eq_comm, union_eq_left_iff_subset]
  refine' subset_trans _ ((M : Matroid α).cl_mono (empty_subset X))
  exact compl_ground_subset_loops_coe _

theorem cl_subset_ground (M : MatroidIn α) (X : Set α) : M.cl X ⊆ M.e :=
  inter_subset_right _ _

theorem subset_cl (hX : X ⊆ M.e) : X ⊆ M.cl X :=
  subset_inter (Matroid.subset_cl M X) hX

theorem RFin.cl (h : M.RFin X) : M.RFin (M.cl X) :=
  ⟨h.to_coe.to_cl.Subset (inter_subset_left _ _), inter_subset_right _ _⟩

theorem rFin_cl_iff (hX : X ⊆ M.e) : M.RFin (M.cl X) ↔ M.RFin X :=
  ⟨fun h => h.Subset (subset_cl hX), RFin.cl⟩

theorem cl_subset_coe_cl (M : MatroidIn α) (X : Set α) : M.cl X ⊆ (M : Matroid α).cl X :=
  inter_subset_left _ _

theorem cl_subset (M : MatroidIn α) (hXY : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
  subset_inter ((M.cl_subset_coe_cl _).trans (Matroid.cl_mono M hXY)) (cl_subset_ground _ _)

theorem cl_subset_inter_ground (M : MatroidIn α) (hXY : X ⊆ Y) : M.cl X ⊆ M.cl Y ∩ M.e :=
  subset_inter (M.cl_subset hXY) (M.cl_subset_ground _)

theorem cl_eq_cl_inter_ground (M : MatroidIn α) (X : Set α) : M.cl X = M.cl (X ∩ M.e) :=
  by
  refine' (M.cl_subset (inter_subset_left _ _)).antisymm' _
  rw [cl, cl, ← union_empty (X ∩ M.E), ← cl_union_cl_right_eq_cl_union]
  refine' inter_subset_inter_left _ ((M : Matroid α).cl_mono _)
  rw [union_distrib_right]
  refine' subset_inter (subset_union_left _ _) ((subset_univ X).trans _)
  refine' (union_compl_self M.E).symm.trans_subset (union_subset_union_right _ _)
  exact compl_ground_subset_loops_coe _

@[simp]
theorem cl_cl (M : MatroidIn α) (X : Set α) : M.cl (M.cl X) = M.cl X :=
  by
  refine' (subset_cl (M.cl_subset_ground X)).antisymm' (subset_inter _ (M.cl_subset_ground _))
  refine' (inter_subset_left _ _).trans _
  rw [← Matroid.cl_cl (M : Matroid α) X]
  exact Matroid.cl_mono _ (M.cl_subset_coe_cl X)

theorem subset_cl_of_subset (hX : X ⊆ M.e) (h : X ⊆ Y) : X ⊆ M.cl Y :=
  (subset_cl hX).trans (M.cl_subset h)

theorem subset_cl_iff_cl_subset_cl (hX : X ⊆ M.e) : X ⊆ M.cl Y ↔ M.cl X ⊆ M.cl Y :=
  ⟨fun h => inter_subset_inter (Matroid.cl_subset_cl (h.trans (M.cl_subset_coe_cl _))) Subset.rfl,
    fun h => subset_trans (subset_cl hX) h⟩

theorem cl_union_cl_right_eq_cl (M : MatroidIn α) (X Y : Set α) :
    M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [eq_comm, cl, ← cl_union_cl_right_eq_cl_union, ← cl, eq_comm, cl_eq_cl_inter_ground, eq_comm,
    cl_eq_cl_inter_ground, inter_distrib_right, ← cl, inter_distrib_right,
    inter_eq_self_of_subset_left (M.cl_subset_ground Y)]

theorem cl_union_cl_left_eq_cl (M : MatroidIn α) (X Y : Set α) : M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) :=
  by rw [union_comm, cl_union_cl_right_eq_cl, union_comm]

@[simp]
theorem cl_diff_loops_eq_cl (M : MatroidIn α) (X : Set α) : M.cl (X \ M.cl ∅) = M.cl X := by
  rw [← union_empty (X \ M.cl ∅), ← cl_union_cl_right_eq_cl, diff_union_self,
    cl_union_cl_right_eq_cl, union_empty]

theorem Indep.mem_cl_iff_of_not_mem (hI : M.indep I) (he : e ∈ M.e \ I) :
    e ∈ M.cl I ↔ ¬M.indep (insert e I) := by
  rw [cl_eq_coe_cl_inter, mem_inter_iff, iff_true_intro he.1, and_true_iff,
    Matroid.Indep.mem_cl_iff_of_not_mem hI he.2, indep_iff_coe]

theorem Indep.not_mem_cl_iff_of_not_mem (hI : M.indep I) (he : e ∈ M.e \ I) :
    e ∉ M.cl I ↔ M.indep (insert e I) := by rw [hI.mem_cl_iff_of_not_mem he, Classical.not_not]

theorem mem_cl_iff_exists_circuit_of_not_mem (he : e ∈ M.e \ X) :
    e ∈ M.cl X ↔ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X :=
  by
  simp_rw [cl_eq_coe_cl_inter, mem_inter_iff, iff_true_intro he.1, and_true_iff,
    Matroid.mem_cl_iff_exists_circuit_of_not_mem he.2, circuit_coe_iff]
  apply exists_congr fun C => _
  simp only [mem_compl_iff, exists_prop, and_congr_left_iff, or_iff_left_iff_imp,
    forall_exists_index, and_imp]
  rintro h' - x hx rfl
  rw [← mem_singleton_iff.mp h'] at hx
  exact (hx he.1).elim

theorem Hyperplane.subset_ground (hH : M.Hyperplane H) : H ⊆ M.e :=
  hH.2

theorem Hyperplane.coe_union_hyperplane (hH : M.Hyperplane H) :
    (M : Matroid α).Hyperplane (H ∪ M.eᶜ) :=
  hH.1

theorem hyperplane_iff_coe : M.Hyperplane H ↔ (M : Matroid α).Hyperplane (H ∪ M.eᶜ) ∧ H ⊆ M.e :=
  Iff.rfl

theorem mem_cl_iff_forall_hyperplane (he : e ∈ M.e) (hX : X ⊆ M.e) :
    e ∈ M.cl X ↔ ∀ H, M.Hyperplane H → X ⊆ H → e ∈ H :=
  by
  simp_rw [cl_eq_coe_cl_inter, mem_inter_iff, and_iff_left he, Matroid.mem_cl_iff_forall_hyperplane,
    hyperplane_iff_coe]
  refine'
    ⟨fun h H hH hXH =>
      (h _ hH.1 (hXH.trans (subset_union_left _ _))).elim id fun h' => (h' he).elim,
      fun h H hH hXH => _⟩
  refine' (h (H ∩ M.E) ⟨_, inter_subset_right _ _⟩ (subset_inter hXH hX)).1
  rw [union_distrib_right, union_compl_self, inter_univ]
  convert hH
  rw [union_eq_left_iff_subset, ← hH.flat.cl]
  exact M.compl_ground_subset_loops_coe.trans (Matroid.cl_mono M (empty_subset _))

theorem Basis.subset_cl (hIX : M.Basis I X) : X ⊆ M.cl I :=
  subset_inter (Matroid.Basis.subset_cl hIX.1) hIX.subset_ground

theorem Base.cl (hB : M.base B) : M.cl B = M.e := by rw [cl, Matroid.Base.cl hB, univ_inter]

theorem Basis.cl (hIX : M.Basis I X) : M.cl I = M.cl X := by rw [cl, cl, hIX.to_coe.cl]

theorem Flat.subset_ground (hF : M.Flat F) : F ⊆ M.e :=
  hF.2

theorem Flat.cl (hF : M.Flat F) : M.cl F = F :=
  by
  refine' (subset_cl hF.subset_ground).antisymm' _
  convert inter_subset_inter_left M.E hF.1.cl.Subset using 1
  · convert rfl using 2
    rw [← cl_union_cl_right_eq_cl_union, cl_eq_loops_of_subset (compl_ground_subset_loops_coe _),
      cl_union_cl_right_eq_cl_union, union_empty]
  rw [inter_distrib_right, inter_eq_left_iff_subset.mpr hF.subset_ground, compl_inter_self,
    union_empty]

theorem flat_iff_cl_self : M.Flat F ↔ M.cl F = F :=
  by
  refine' ⟨flat.cl, fun h => _⟩
  rw [cl] at h
  rw [flat, flat_iff_cl_self, cl_union_eq_cl_of_subset_loops M.compl_ground_subset_loops_coe]
  nth_rw 3 [← h]
  nth_rw 1 [← inter_union_compl ((M : Matroid α).cl F) M.E]
  rw [and_iff_left (inter_subset_right _ _), h]
  convert rfl
  rw [eq_comm, inter_eq_right_iff_subset]
  exact M.compl_ground_subset_loops_coe.trans (cl_mono _ (empty_subset _))

theorem flat_of_cl (M : MatroidIn α) (X : Set α) : M.Flat (M.cl X) := by
  rw [flat_iff_cl_self, cl_cl]

/-- Flats of `M : matroid_in α` correspond to those in `(↑M : matroid α)` -/
def flatCoeEquiv (M : MatroidIn α) : { F // M.Flat F } ≃ { F // (M : Matroid α).Flat F }
    where
  toFun F := ⟨F ∪ M.eᶜ, F.2.1⟩
  invFun F :=
    ⟨F ∩ M.e,
      by
      rw [flat, and_iff_left (inter_subset_right _ _), union_distrib_right, union_compl_self,
        inter_univ, union_eq_self_of_subset_right]
      · exact F.2
      exact M.compl_ground_subset_loops_coe.trans F.2.loops_subset⟩
  left_inv := by
    rintro ⟨F, hF⟩
    simp only [coe_mk, inter_distrib_right, compl_inter_self, union_empty,
      inter_eq_self_of_subset_left hF.subset_ground]
  right_inv := by
    rintro ⟨F, hF⟩
    simp only [coe_mk, union_distrib_right, union_compl_self, inter_univ, union_eq_left_iff_subset]
    exact M.compl_ground_subset_loops_coe.trans hF.loops_subset

@[simp]
theorem flatCoeEquiv_apply (M : MatroidIn α) (F : { F // M.Flat F }) :
    (M.flatCoeEquiv F : Set α) = F ∪ M.eᶜ :=
  rfl

@[simp]
theorem flatCoeEquiv_apply_symm (M : MatroidIn α) (F : { F // (M : Matroid α).Flat F }) :
    (M.flatCoeEquiv.symm F : Set α) = F ∩ M.e :=
  rfl

@[simp]
theorem equivSubtype.cl_eq {E : Set α} (X : Set E) (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).cl X = coe ⁻¹' (M : MatroidIn α).cl (coe '' X) :=
  by
  obtain ⟨M, rfl⟩ := M
  rw [coe_mk]
  refine' Set.ext fun e => (em (e ∈ X)).elim (fun he => _) fun he => _
  · refine' iff_of_true (Matroid.mem_cl_of_mem _ he) (MatroidIn.subset_cl _ ⟨e, he, rfl⟩)
    convert image_subset_range _ _
    rw [range_coe]
  rw [Matroid.mem_cl_iff_exists_circuit_of_not_mem he, mem_preimage, cl, mem_inter_iff,
    Matroid.mem_cl_iff_exists_circuit_of_not_mem]
  · simp only [equiv_subtype.circuit_iff, coe_mk, coe_prop, and_true_iff, ← image_insert_eq]
    constructor
    · rintro ⟨C, hC, heC, hC'⟩
      exact ⟨coe '' C, hC.to_coe, ⟨e, heC, rfl⟩, image_subset _ hC'⟩
    rintro ⟨C, hC, heC, hC'⟩
    obtain ⟨C₀, rfl⟩ := subset_range_iff_exists_image_eq.mp (hC'.trans (image_subset_range _ _))
    rw [image_subset_image_iff coe_injective] at hC'
    rw [coe_injective.mem_set_image] at heC
    exact ⟨C₀, ⟨hC, (image_subset_range _ _).trans_eq range_coe⟩, heC, hC'⟩
  rwa [coe_injective.mem_set_image]

@[simp]
theorem equivSubtype.symm_cl_eq {E X : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).cl X = coe '' M.cl (coe ⁻¹' X) :=
  by
  set N := equiv_subtype.symm M with hN
  have hM : M = equiv_subtype N; rw [hN, Equiv.apply_symm_apply]
  rw [hM, equiv_subtype.cl_eq, image_preimage_eq_inter_range, image_preimage_eq_inter_range,
    inter_eq_self_of_subset_left, cl_eq_cl_inter_ground, range_coe]
  · convert rfl
  rw [range_coe]
  convert cl_subset_ground _ _

@[simp]
theorem equivSubtype.flat_iff {E : Set α} {F : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).Flat F ↔ (M : MatroidIn α).Flat (coe '' F) :=
  by
  rw [flat_iff_cl_self, Matroid.flat_iff_cl_self, equiv_subtype.cl_eq, ←
    image_eq_image coe_injective, image_preimage_eq_iff.mpr]
  convert cl_subset_ground _ _
  rw [range_coe]
  exact M.2.symm

@[simp]
theorem equivSubtype.symm_flat_iff {E F : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Flat F ↔ M.Flat (coe ⁻¹' F) ∧ F ⊆ E :=
  by
  rw [← Equiv.apply_symm_apply equiv_subtype M, equiv_subtype.flat_iff, Equiv.apply_symm_apply,
    image_preimage_coe]
  refine' ⟨fun h => _, _⟩
  · have hFE : F ⊆ E := h.subset_ground
    exact ⟨by rwa [inter_eq_self_of_subset_left hFE], hFE⟩
  rintro ⟨h₁, h₂⟩
  rwa [inter_eq_self_of_subset_left h₂] at h₁

theorem equivSubtype.symm_flat_iff_exists {E F : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Flat F ↔ ∃ F₀, M.Flat F₀ ∧ F = coe '' F₀ :=
  by
  rw [equiv_subtype.symm_flat_iff]
  refine'
    ⟨fun h =>
      ⟨_, h.1, by
        rw [eq_comm, image_preimage_eq_iff, range_coe]
        exact h.2⟩,
      _⟩
  rintro ⟨F₀, hF₀, rfl⟩
  simp_rw [preimage_image_eq _ coe_injective, ← @range_coe _ E]
  exact ⟨hF₀, image_subset_range _ _⟩

theorem flat_eq_transferSetProp (M : MatroidIn α) :
    M.Flat = TransferSetProp (fun _ => Matroid.Flat) M :=
  by
  ext F
  simp only [transfer_set_prop_iff, equiv_subtype.flat_iff, coe_mk, image_preimage_coe]
  exact
    ⟨fun h => ⟨by rwa [inter_eq_self_of_subset_left h.subset_ground], h.subset_ground⟩, fun h =>
      by
      rw [← inter_eq_self_of_subset_left h.2]
      exact h.1⟩

theorem Flat.exists_eq_coe (h : M.Flat F) :
    ∃ F₀ : Set M.e, (equivSubtype ⟨M, rfl⟩).Flat F₀ ∧ F = coe '' F₀ :=
  by
  rw [flat_eq_transfer_set_prop] at h
  exact h.exists_eq_coe

def Covby (M : MatroidIn α) :=
  TransferSetProp₂ (fun _ => Matroid.Covby) M

-- lemma covby_iff : M.covby F₁ F₂ ↔ M.flat F₁ ∧ M.flat F₂ ∧ F₁ ⊂ F₂ ∧
--   ∀ F, M.flat F → F₁ ⊆ F → F ⊆ F₂ → F = F₁ ∨ F = F₂ :=
-- begin
--   split,
--   { revert F₁ F₂,
--     simp_rw [covby, transfer_set_prop₂_forall_iff, matroid.covby_iff,
--       equiv_subtype.flat_iff, coe_mk, flat_eq_transfer_set_prop, transfer_set_prop_forall_iff,
--       ssubset_iff_subset_not_subset, image_coe_subset_image_coe_iff, image_coe_eq_image_coe_iff,
--       ←flat_eq_transfer_set_prop, equiv_subtype.flat_iff, coe_mk],
--     exact λ _ _, id },
--   simp_rw [and_imp, flat_eq_transfer_set_prop, covby],
--   revert F₁,
--   simp,
--   -- simp only [transfer_set_prop_forall_iff, equiv_subtype.flat_iff, coe_mk, image_subset_iff,
--   --   image_coe_subset_image_coe_iff, image_coe_eq_image_coe_iff],
--   -- rw [and_imp, and_imp, flat_eq_transfer_set_prop],
--   -- revert F₁ F₂,
--   -- revert F₁,
--   simp only [transfer_set_prop_forall_iff, equiv_subtype.flat_iff, coe_mk, image_subset_iff, and_imp],
--   simp only [flat_eq_transfer_set_prop], simp,
-- --     },
--   -- rw [covby, iff_def],
--   refine ⟨λ h, _, λ h, _⟩,
--   { obtain ⟨F₁,F₂,hc,rfl,rfl⟩ := h.exists_eq_coe,
--     simp_rw [matroid.covby_iff, equiv_subtype.flat_iff, coe_mk, ssubset_iff_subset_not_subset]
--       at hc,
--     simp_rw [ssubset_iff_subset_not_subset, image_subset_image_iff coe_injective],
--     refine ⟨hc.1, hc.2.1, hc.2.2.1, λ F hF hF₁F hFF₂, _ ⟩,
--     obtain ⟨F, hF', rfl⟩ := hF.exists_eq_coe,
--     rw [image_subset_image_iff coe_injective] at hF₁F hFF₂,
--     simp_rw [image_eq_image coe_injective],
--     exact hc.2.2.2 F hF hF₁F hFF₂ },
--   obtain ⟨F₁, hF₁, rfl⟩ := h.1.exists_eq_coe,
--   obtain ⟨F₂, hF₂, rfl⟩ := h.2.1.exists_eq_coe,
--   simp only [covby, transfer_set_prop₂_iff, matroid.covby_iff, preimage_image_coe,
--     equiv_subtype.flat_iff, coe_mk, image_subset_iff, coe_preimage_self, subset_univ, and_true,
--     ssubset_iff_subset_not_subset],
--   simp_rw [ssubset_iff_subset_not_subset, image_coe_subset_image_coe_iff] at h,
--   -- refine (em (F₁ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₁E, _),
--   -- { rw [covby, transfer_set_prop₂_iff], tauto },
--   -- { exact λ h, hnss h.1.subset_ground },
--   -- refine (em (F₂ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₂E, _),
--   -- { rw [covby, transfer_set_prop₂_iff], tauto },
--   -- { exact λ h, hnss h.2.1.subset_ground },
--   -- rw [←@range_coe _ M.E] at hF₁E hF₂E,
--   -- obtain ⟨F₁, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₁E,
--   -- obtain ⟨F₂, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₂E,
--   simp only [covby, matroid.covby_iff, transfer_set_prop₂_iff, preimage_image_coe,
--     equiv_subtype.flat_iff, coe_mk, image_subset_iff, coe_preimage_self, subset_univ, and_true,
--     and.congr_right_iff, ssubset_iff_subset_not_subset, image_subset_image_iff coe_injective],
--   refine λ hF₁ hF₂ hss, ⟨λ h F hF hF₁F hFF₂, _, λ h, _⟩,
--   -- have := h (coe ⁻¹' F),
--   -- simp_rw [covby, transfer_set_prop₂_iff, matroid.covby_iff, equiv_subtype.flat_iff, coe_mk,
--   --   image_preimage_coe, inter_eq_self_of_subset_left hF₁E, inter_eq_self_of_subset_left hF₂E,
--   --   and_iff_right hF₁E, and_iff_left hF₂E, and.congr_right_iff],
--   -- refine (em (F₁ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₁E, _),
--   -- { rw [covby, transfer_set_prop₂_iff], tauto },
--   -- { exact λ h, hnss h.1.subset_ground },
--   -- refine (em (F₂ ⊆ M.E)).symm.elim (λ hnss, iff_of_false _ _) (λ hF₂E, _),
--   -- { rw [covby, transfer_set_prop₂_iff], tauto },
--   -- { exact λ h, hnss h.2.1.subset_ground },
--   -- rw [←@range_coe _ M.E] at hF₁E hF₂E,
--   -- obtain ⟨F₁, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₁E,
--   -- obtain ⟨F₂, rfl⟩ := subset_range_iff_exists_image_eq.mp hF₂E,
--   -- simp_rw [covby, flat_eq_transfer_set_prop, transfer_set_prop₂_coe_iff,
--   --   transfer_set_prop_coe_iff, matroid.covby_iff, equiv_subtype.flat_iff, coe_mk],
--   --   simp,
--   -- -- squeeze_simp [covby, matroid.covby_iff],
--   -- simp_rw [covby, transfer_set_prop₂_iff, matroid.covby_iff, equiv_subtype.flat_iff, coe_mk,
--   --   image_preimage_coe, inter_eq_self_of_subset_left hF₁E, inter_eq_self_of_subset_left hF₂E,
--   --   and_iff_right hF₁E, and_iff_left hF₂E, and.congr_right_iff],
--   -- -- have := matroid.covby_iff,
-- end
theorem Covby.flat_left (h : M.Covby F₁ F₂) : M.Flat F₁ :=
  by
  rw [← h.inter_ground_left]
  simp only [Covby, transfer_set_prop₂_iff] at h
  simpa using h.1.flat_left

theorem Covby.flat_right (h : M.Covby F₁ F₂) : M.Flat F₂ :=
  by
  rw [← h.inter_ground_right]
  simp only [Covby, transfer_set_prop₂_iff] at h
  simpa using h.1.flat_right

-- lemma covby.ssubset (h : M.covby F₁ F₂) : F₁ ⊂ F₂ :=
-- begin
-- end
-- ### loops and nonloops
/-- A `loop` is a dependent singleton (that is contained in the ground set )-/
def Loop (M : MatroidIn α) (e : α) : Prop :=
  (M : Matroid α).Loop e ∧ e ∈ M.e

/-- A `nonloop` is an independent singleton -/
def Nonloop (M : MatroidIn α) (e : α) : Prop :=
  (M : Matroid α).Nonloop e

/-- A `coloop` is a loop of the dual matroid -/
def Coloop (M : MatroidIn α) (e : α) : Prop :=
  (M : Matroid α).Coloop e

theorem Loop.mem_ground (he : M.Loop e) : e ∈ M.e :=
  he.2

theorem Loop.dep (he : M.Loop e) : ¬M.indep {e} :=
  Matroid.Loop.dep he.1

theorem Loop.to_coe (he : M.Loop e) : (M : Matroid α).Loop e :=
  he.1

theorem loop_iff_dep (he : e ∈ M.e) : M.Loop e ↔ ¬M.indep {e} :=
  ⟨Loop.dep, fun h => ⟨Matroid.loop_iff_dep.mpr h, he⟩⟩

theorem loop_iff_circuit : M.Loop e ↔ M.Circuit {e} :=
  by
  refine'
    (em (e ∈ M.E)).symm.elim
      (fun he =>
        iff_of_false (fun hl => he hl.mem_ground) fun hC => he (hC.subset_ground (mem_singleton e)))
      fun he => _
  rw [loop_iff_dep he, circuit, indep_iff_coe, circuit_iff_dep_forall_diff_singleton_indep,
    and_assoc']
  simp only [indep_singleton, not_nonloop_iff, mem_singleton_iff, forall_eq, diff_self, empty_indep,
    singleton_subset_iff, true_and_iff, iff_self_and, iff_true_intro he, imp_true_iff]

theorem loop_iff_mem_cl_empty : M.Loop e ↔ e ∈ M.cl ∅ :=
  Iff.rfl

theorem nonloop_iff_coe (e : α) : M.Nonloop e ↔ (M : Matroid α).Nonloop e :=
  Iff.rfl

theorem Nonloop.to_coe (he : M.Nonloop e) : (M : Matroid α).Nonloop e :=
  he

@[simp]
theorem indep_singleton : M.indep {e} ↔ M.Nonloop e :=
  Matroid.indep_singleton

alias indep_singleton ↔ indep.nonloop nonloop.indep

@[simp]
theorem equivSubtype.nonloop_iff {E : Set α} {M : { M : MatroidIn α // M.e = E }} {e : E} :
    (equivSubtype M).Nonloop e ↔ (M : MatroidIn α).Nonloop (e : α) := by
  simp [← Matroid.indep_singleton]

@[simp]
theorem equivSubtype.symm_nonloop_iff {E : Set α} {M : Matroid E} {e : α} :
    (equivSubtype.symm M : MatroidIn α).Nonloop e ↔ ∃ f, M.Nonloop f ∧ e = f :=
  by
  simp_rw [← indep_singleton, equiv_subtype.symm_indep_iff, singleton_subset_iff, ←
    Matroid.indep_singleton, ← @range_coe _ E, mem_range]
  constructor
  · rintro ⟨hi, ⟨y, rfl⟩⟩
    rw [← image_singleton, preimage_image_coe] at hi
    exact ⟨_, hi, rfl⟩
  rintro ⟨f, hf, rfl⟩
  rw [← image_singleton, preimage_image_coe]
  exact ⟨hf, _, rfl⟩

-- by simp_rw [←indep_singleton, equiv_subtype.symm_indep_iff, ←image_singleton, preimage_image_coe,
--     ←@range_coe _ E, and_iff_left (image_subset_range _ _), matroid.indep_singleton]
attribute [protected] indep.nonloop nonloop.indep

theorem Nonloop.mem_ground (he : M.Nonloop e) : e ∈ M.e :=
  singleton_subset_iff.mp he.indep.subset_ground

theorem nonloop_of_not_mem_cl (he : e ∈ M.e) (h : e ∉ M.cl X) : M.Nonloop e :=
  nonloop_of_not_mem_cl fun h' => h ⟨h', he⟩

/-- A `loopless` matroid is one with no loop-/
def Loopless (M : MatroidIn α) :=
  ∀ e ∈ M.e, M.Nonloop e

@[simp]
theorem equivSubtype.loopless_iff {E : Set α} {M : { M : MatroidIn α // M.e = E }} :
    (equivSubtype M).Loopless ↔ (M : MatroidIn α).Loopless :=
  by
  obtain ⟨M, rfl⟩ := M
  simp [loopless, Matroid.Loopless]

theorem loopless_iff_girth_ne_one : M.Loopless ↔ M.girth ≠ 1 :=
  by
  convert(@equiv_subtype.loopless_iff _ _ ⟨M, rfl⟩).symm
  rw [loopless_iff_girth_ne_one, girth]

theorem loopless_iff_forall_circuit : M.Loopless ↔ ∀ C, M.Circuit C → C.Finite → 1 < C.ncard :=
  by
  convert(@equiv_subtype.loopless_iff _ _ ⟨M, rfl⟩).symm
  simp_rw [loopless_iff_forall_circuit, equiv_subtype.circuit_iff, coe_mk, eq_iff_iff]
  refine' ⟨fun h C hC hCfin => _, fun h C hC hCfin => _⟩
  · rw [← ncard_image_of_injective C coe_injective]
    exact h _ hC (hCfin.image coe)
  have hcoe : (coe : M.E → α) '' (coe ⁻¹' C) = C :=
    by
    rw [image_preimage_eq_iff, range_coe]
    exact hC.subset_ground
  convert h (coe ⁻¹' C) _ (hCfin.preimage (coe_injective.inj_on _)) using 1
  · rw [← ncard_image_of_injective _ coe_injective, hcoe]
  rwa [hcoe]

@[simp]
theorem equivSubtype.symm_loopless_iff {E : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).Loopless ↔ M.Loopless :=
  by
  rw [loopless_iff_girth_ne_one, Matroid.loopless_iff_girth_ne_one, girth]
  simp

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (e f «expr ∈ » M.E) -/
/-- A `simple` matroid is one with no parallel pair -/
def Simple (M : MatroidIn α) :=
  ∀ (e) (_ : e ∈ M.e) (f) (_ : f ∈ M.e), M.indep {e, f}

@[simp]
theorem equivSubtype.simple_iff {E : Set α} {M : { M : MatroidIn α // M.e = E }} :
    (equivSubtype M).simple ↔ (M : MatroidIn α).simple :=
  by
  obtain ⟨M, rfl⟩ := M
  simp [simple, Matroid.Simple, image_pair]

theorem simple_iff_girth : M.simple ↔ M.girth = 0 ∨ 2 < M.girth :=
  by
  convert(@equiv_subtype.simple_iff _ _ ⟨M, rfl⟩).symm
  rw [eq_iff_iff, Matroid.simple_iff_girth, girth]

@[simp]
theorem equivSubtype.symm_simple_iff {E : Set α} (M : Matroid E) :
    (equivSubtype.symm M : MatroidIn α).simple ↔ M.simple := by
  rw [simple_iff_girth, Matroid.simple_iff_girth, girth, coe_eta, Equiv.apply_symm_apply]

/-! Rank -/


/-- The rank of a set `X`. This is equal to the rank of `X ∩ M.E` in the coercion. -/
noncomputable def r (M : MatroidIn α) (X : Set α) :=
  (M : Matroid α).R X

/-- The rank of the ground set `M.E` -/
noncomputable def rk (M : MatroidIn α) : ℕ :=
  (M : Matroid α).rk

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem le_r_iff {n : ℕ} [Finite α] : n ≤ M.R X ↔ ∃ (I : _)(_ : I ⊆ X), M.indep I ∧ I.ncard = n :=
  Matroid.le_r_iff

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » X) -/
theorem r_le_iff {n : ℕ} [Finite α] : M.R X ≤ n ↔ ∀ (I) (_ : I ⊆ X), M.indep I → I.ncard ≤ n :=
  Matroid.r_le_iff

theorem r_eq_coe_r (X : Set α) : M.R X = (M : Matroid α).R X :=
  rfl

@[simp]
theorem r_compl_ground : M.R (M.eᶜ) = 0 :=
  r_eq_zero_of_subset_loops (compl_ground_subset_loops_coe _)

theorem coe_r_compl_ground (M : MatroidIn α) : (M : Matroid α).R (M.eᶜ) = 0 :=
  r_compl_ground

theorem r_eq_r_inter_ground (X : Set α) : M.R X = M.R (X ∩ M.e) := by
  rw [r_eq_coe_r, ← Matroid.r_cl, ←
    Matroid.cl_diff_eq_cl_of_subset_loops M.compl_ground_subset_loops_coe X, diff_eq, compl_compl,
    Matroid.r_cl, ← r_eq_coe_r]

@[simp]
theorem coe_r_union_compl_ground (M : MatroidIn α) (X : Set α) :
    (M : Matroid α).R (X ∪ M.eᶜ) = M.R X := by
  rw [← r, r_eq_r_inter_ground, inter_distrib_right, compl_inter_self, union_empty, ←
    r_eq_r_inter_ground]

@[simp]
theorem r_union_compl_ground (M : MatroidIn α) (X : Set α) : M.R (X ∪ M.eᶜ) = M.R X :=
  M.coe_r_union_compl_ground X

theorem rk_eq_rk_coe (M : MatroidIn α) : M.rk = (M : Matroid α).rk :=
  rfl

theorem rk_eq_r_ground (M : MatroidIn α) : M.rk = M.R M.e := by
  rw [rk, Matroid.rk_def, ← r_eq_coe_r, r_eq_r_inter_ground, univ_inter]

@[simp]
theorem r_cl (M : MatroidIn α) (X : Set α) : M.R (M.cl X) = M.R X := by
  rw [r, r, ← (M : Matroid α).r_cl X, cl, ← r, ← r, ← r_eq_r_inter_ground]

@[simp]
theorem r_empty (M : MatroidIn α) : M.R ∅ = 0 :=
  Matroid.r_empty M

theorem Indep.r (hI : M.indep I) : M.R I = I.ncard :=
  Matroid.Indep.r hI

theorem indep_iff_r_eq_card [Finite α] : M.indep I ↔ M.R I = I.ncard :=
  Matroid.indep_iff_r_eq_card

theorem indep_iff_r_eq_card_of_finite (hI : I.Finite) : M.indep I ↔ M.R I = I.ncard :=
  Matroid.indep_iff_r_eq_card_of_finite hI

theorem Basis.r (hIX : M.Basis I X) : M.R I = M.R X :=
  Matroid.Basis.r hIX.to_coe

theorem Basis.card (hIX : M.Basis I X) : I.ncard = M.R X :=
  Matroid.Basis.card hIX.to_coe

theorem Nonloop.r (he : M.Nonloop e) : M.R {e} = 1 :=
  he.R

@[simp]
theorem equivSubtype.r_eq {E : Set α} (M : { M : MatroidIn α // M.e = E }) (X : Set E) :
    (equivSubtype M).R X = (M : MatroidIn α).R (coe '' X) := by simp [equiv_subtype_apply, r]

@[simp]
theorem equivSubtype.symm_r_eq {E : Set α} (M : Matroid E) (X : Set α) :
    (equivSubtype.symm M : MatroidIn α).R X = M.R (coe ⁻¹' X) := by
  simp [r, equiv_subtype_apply_symm_coe_coe]

-- ### Cocircuits etc
/-- A `cocircuit` is a minimal transversal of bases. -/
def Cocircuit (M : MatroidIn α) (K : Set α) :=
  (M : Matroid α).Cocircuit K

/-- A `coindep`endent set is one whose complement (relative to the ground set) contains a base -/
def Coindep (M : MatroidIn α) (X : Set α) :=
  (M : Matroid α).Coindep X ∧ X ⊆ M.e

theorem cocircuit_iff_coe (K : Set α) : M.Cocircuit K ↔ (M : Matroid α).Cocircuit K :=
  Iff.rfl

theorem Cocircuit.subset_ground (hK : M.Cocircuit K) : K ⊆ M.e := fun x hx =>
  MatroidIn.Nonloop.mem_ground (hK.nonloop_of_mem hx)

theorem cocircuit_iff_mem_minimals :
    M.Cocircuit K ↔ K ∈ minimals (· ⊆ ·) { X | ∀ B, M.base B → (B ∩ X).Nonempty } := by
  simp_rw [cocircuit, Matroid.cocircuit_iff_mem_minimals, base_iff_coe]

theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.e :=
  hX.2

theorem coindep_iff_disjoint_base : M.Coindep X ↔ ∃ B, M.base B ∧ X ⊆ M.e \ B :=
  by
  simp_rw [coindep, Matroid.coindep_iff_disjoint_base, ← base_iff_coe, subset_diff]
  tauto

theorem Coindep.to_coe (h : M.Coindep X) : (M : Matroid α).Coindep X :=
  h.1

theorem coindep_forall_subset_not_cocircuit (hX : X ⊆ M.e) :
    M.Coindep X ↔ ∀ ⦃K⦄, K ⊆ X → ¬M.Cocircuit K := by
  simp_rw [coindep, Matroid.coindep_iff_forall_subset_not_cocircuit, iff_true_intro hX,
    and_true_iff, cocircuit]

theorem coindep_iff_cl_compl_eq_ground (hX : X ⊆ M.e) : M.Coindep X ↔ M.cl (M.e \ X) = M.e :=
  by
  rw [coindep, Matroid.coindep_iff_cl_compl_eq_univ, cl_coe_eq, cl_eq_cl_inter_ground, ←
    diff_eq_compl_inter, ← (true_iff_iff _).mpr hX, and_true_iff]
  refine' ⟨fun hu => (cl_subset_ground _ _).antisymm _, fun h => _⟩
  ·
    rwa [← compl_compl (M.cl _), ← compl_inter, ← compl_inj_iff, compl_univ, compl_compl, ←
      disjoint_iff_inter_eq_empty, disjoint_compl_left_iff_subset] at hu
  rw [h, union_compl_self]

theorem compl_hyperplane_iff_cocircuit (hK : K ⊆ M.e) : M.Hyperplane (M.e \ K) ↔ M.Cocircuit K := by
  rw [cocircuit, ← Matroid.compl_hyperplane_iff_cocircuit, hyperplane,
    and_iff_left (diff_subset _ _), diff_eq, union_distrib_right, union_compl_self, univ_inter, ←
    compl_inter, inter_eq_self_of_subset_left hK]

theorem compl_cocircuit_iff_hyperplane (hH : H ⊆ M.e) : M.Cocircuit (M.e \ H) ↔ M.Hyperplane H := by
  rw [← compl_hyperplane_iff_cocircuit (diff_subset _ _), diff_diff_cancel_left hH]

theorem Cocircuit.compl_hyperplane (hK : M.Cocircuit K) : M.Hyperplane (M.e \ K) :=
  (compl_hyperplane_iff_cocircuit hK.subset_ground).mpr hK

theorem Hyperplane.compl_cocircuit (hH : M.Hyperplane H) : M.Cocircuit (M.e \ H) :=
  (compl_cocircuit_iff_hyperplane hH.subset_ground).mpr hH

/-! ### Skewness -/


/-- Two sets are `skew` if contracting one does not affect the restriction to the other. -/
def Skew (M : MatroidIn α) (X Y : Set α) :=
  (M : Matroid α).Skew X Y ∧ X ⊆ M.e ∧ Y ⊆ M.e

theorem Skew.to_coe (h : M.Skew X Y) : (M : Matroid α).Skew X Y :=
  h.1

theorem Skew.left_subset_ground (h : M.Skew X Y) : X ⊆ M.e :=
  h.2.1

theorem Skew.right_subset_ground (h : M.Skew X Y) : Y ⊆ M.e :=
  h.2.2

theorem Skew.symm (h : M.Skew X Y) : M.Skew Y X :=
  ⟨h.to_coe.symm, h.2.2, h.2.1⟩

theorem Skew.comm : M.Skew X Y ↔ M.Skew Y X :=
  ⟨Skew.symm, Skew.symm⟩

theorem Skew.subset_left (h : M.Skew X Y) {X' : Set α} (hX'X : X' ⊆ X) : M.Skew X' Y :=
  ⟨h.to_coe.subset_left hX'X, hX'X.trans h.2.1, h.2.2⟩

theorem Skew.subset_right (h : M.Skew X Y) {Y' : Set α} (hY'Y : Y' ⊆ Y) : M.Skew X Y' :=
  ⟨h.to_coe.subset_right hY'Y, h.2.1, hY'Y.trans h.2.2⟩

theorem Skew.r_add [FiniteRk M] (h : M.Skew X Y) : M.R X + M.R Y = M.R (X ∪ Y) :=
  h.to_coe.r_add

theorem skew_iff_r [FiniteRk M] (hX : X ⊆ M.e) (hY : Y ⊆ M.e) :
    M.Skew X Y ↔ M.R X + M.R Y = M.R (X ∪ Y) :=
  ⟨Skew.r_add, fun h => ⟨Matroid.skew_iff_r.mpr h, hX, hY⟩⟩

theorem Skew.cl_left (h : M.Skew X Y) : M.Skew (M.cl X) Y :=
  ⟨h.to_coe.cl_left.subset_left (M.cl_subset_coe_cl _), M.cl_subset_ground X, h.2.2⟩

theorem Skew.cl_right (h : M.Skew X Y) : M.Skew X (M.cl Y) :=
  h.symm.cl_left.symm

theorem skew_iff_cl_left (hX : X ⊆ M.e) : M.Skew X Y ↔ M.Skew (M.cl X) Y :=
  ⟨Skew.cl_left, fun h => h.subset_left (subset_cl hX)⟩

theorem skew_iff_cl_right (hY : Y ⊆ M.e) : M.Skew X Y ↔ M.Skew X (M.cl Y) :=
  ⟨Skew.cl_right, fun h => h.subset_right (subset_cl hY)⟩

theorem Skew.inter_subset_loops (h : M.Skew X Y) : X ∩ Y ⊆ M.cl ∅ :=
  subset_inter (Matroid.Skew.inter_subset_loops h.1)
    ((inter_subset_right _ _).trans h.right_subset_ground)

theorem Skew.disjoint_of_indep_left (h : M.Skew I X) (hI : M.indep I) : Disjoint I X :=
  h.to_coe.disjoint_of_indep_left hI

theorem Skew.disjoint_of_indep_right (h : M.Skew X I) (hI : M.indep I) : Disjoint X I :=
  (h.symm.disjoint_of_indep_left hI).symm

theorem skew_iff_disjoint_of_union_indep (h : M.indep (I ∪ J)) : M.Skew I J ↔ Disjoint I J := by
  rw [← Matroid.skew_iff_disjoint_of_union_indep h, skew, ← union_subset_iff,
    and_iff_left h.subset_ground]

theorem Indep.skew_diff_of_subset (hI : M.indep I) (hJ : J ⊆ I) : M.Skew J (I \ J) :=
  ⟨Matroid.Indep.skew_diff_of_subset hI hJ, hJ.trans hI.subset_ground,
    (diff_subset _ _).trans hI.subset_ground⟩

theorem Skew.diff_loops_disjoint_left (h : M.Skew X Y) : Disjoint (X \ M.cl ∅) Y :=
  by
  convert Matroid.Skew.diff_loops_disjoint_left h.1 using 1
  rw [cl_coe_eq, ← diff_diff, diff_eq, diff_eq, compl_compl, eq_comm, inter_eq_left_iff_subset]
  exact (inter_subset_left _ _).trans h.left_subset_ground

theorem Skew.diff_loops_disjoint_right (h : M.Skew X Y) : Disjoint X (Y \ M.cl ∅) :=
  h.symm.diff_loops_disjoint_left.symm

theorem skew_iff_diff_loops_skew_left : M.Skew X Y ↔ M.Skew (X \ M.cl ∅) Y :=
  by
  refine'
    (em (X ⊆ M.E)).symm.elim
      (fun hX => iff_of_false (fun h' => hX h'.left_subset_ground) fun h' => hX _) fun hX => _
  · have h'' := h'.left_subset_ground
    rwa [diff_subset_iff, union_eq_self_of_subset_left (M.cl_subset_ground _)] at h''
  rw [Iff.comm, skew_iff_cl_left ((diff_subset _ _).trans hX), cl_diff_loops_eq_cl, ←
    skew_iff_cl_left hX]

theorem Skew.union_indep (h : M.Skew I J) (hI : M.indep I) (hJ : M.indep J) : M.indep (I ∪ J) :=
  h.to_coe.union_indep hI hJ

theorem Nonloop.singleton_skew_iff (he : M.Nonloop e) (hX : X ⊆ M.e) : M.Skew {e} X ↔ e ∉ M.cl X :=
  by
  rw [skew, he.to_coe.singleton_skew_iff, singleton_subset_iff, cl_eq_coe_cl_inter, mem_inter_iff, ←
    (true_iff_iff _).mpr hX, and_true_iff, ← (true_iff_iff _).mpr he.mem_ground, and_true_iff,
    and_true_iff]

theorem Nonloop.skew_singleton_iff (he : M.Nonloop e) (hX : X ⊆ M.e) : M.Skew X {e} ↔ e ∉ M.cl X :=
  by rw [skew.comm, he.singleton_skew_iff hX]

-- TODO : hyperplanes, flats, cl definitions are equivalent to the usual ones.
theorem eq_of_coe_eq_coe {M₁ M₂ : MatroidIn α} (h : M₁.e = M₂.e) (h' : (M₁ : Matroid α) = M₂) :
    M₁ = M₂ := by
  ext
  rw [ground_eq_E, h, ground_eq_E]
  simp_rw [carrier_eq_coe, h']

theorem eq_iff_coe_eq_coe {M₁ M₂ : MatroidIn α} : M₁.e = M₂.e ∧ (M₁ : Matroid α) = M₂ ↔ M₁ = M₂ :=
  ⟨fun h => eq_of_coe_eq_coe h.1 h.2, by
    rintro rfl
    simp⟩

end Basic

section Ext

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (B «expr ⊆ » M₁.E) -/
theorem eq_of_base_iff_base_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h' : ∀ (B) (_ : B ⊆ M₁.e), M₁.base B ↔ M₂.base B) : M₁ = M₂ :=
  by
  ext; rw [ground_eq_E, hE, ← ground_eq_E]
  exact
    ⟨fun h => (h' _ (base.subset_ground h)).mp h, fun h =>
      (h' _ ((base.subset_ground h).trans_eq hE.symm)).mpr h⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (I «expr ⊆ » M₁.E) -/
theorem eq_of_indep_iff_indep_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h' : ∀ (I) (_ : I ⊆ M₁.e), M₁.indep I ↔ M₂.indep I) : M₁ = M₂ :=
  by
  refine' eq_of_base_iff_base_forall hE fun B hB => _
  simp_rw [base_iff_coe, base_iff_maximal_indep, ← indep_iff_coe]
  exact
    ⟨fun h =>
      ⟨by
        rw [← h' _ h.1.subset_ground]
        exact h.1, fun I hI hBI => h.2 _ (by rwa [h' _ (hI.subset_ground.trans_eq hE.symm)]) hBI⟩,
      fun h =>
      ⟨by
        rw [h' _ (h.1.subset_ground.trans_eq hE.symm)]
        exact h.1, fun I hI hBI => h.2 _ (by rwa [← h' _ hI.subset_ground]) hBI⟩⟩

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (X «expr ⊆ » M₁.E) -/
theorem eq_of_cl_eq_cl_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h : ∀ (X) (_ : X ⊆ M₁.e), M₁.cl X = M₂.cl X) : M₁ = M₂ :=
  by
  refine' eq_of_indep_iff_indep_forall hE fun I hI => _
  simp_rw [indep_iff_coe, indep_iff_not_mem_cl_diff_forall, cl_coe_eq, hE]
  refine' ⟨fun h' e heI => _, fun h' e heI => _⟩
  · rw [← h _ ((diff_subset I {e}).trans hI)]
    exact h' _ heI
  rw [h _ ((diff_subset I {e}).trans hI)]; exact h' _ heI

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (X «expr ⊆ » M₁.E) -/
theorem eq_of_mem_cl_iff_mem_cl_forall {M₁ M₂ : MatroidIn α} (hE : M₁.e = M₂.e)
    (h : ∀ (X) (_ : X ⊆ M₁.e), ∀ e ∈ M₁.e, e ∈ M₁.cl X ↔ e ∈ M₂.cl X) : M₁ = M₂ :=
  by
  refine' eq_of_cl_eq_cl_forall hE fun X hX => _
  rw [← inter_eq_self_of_subset_left (M₁.cl_subset_ground X), ←
    inter_eq_self_of_subset_left (M₂.cl_subset_ground X)]
  simp_rw [Set.ext_iff, mem_inter_iff, hE, and_congr_left_iff, ← hE]
  exact h X hX

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (X «expr ⊆ » M₁.E) -/
theorem eq_of_r_eq_r_forall {M₁ M₂ : MatroidIn α} [FiniteRk M₁] (hE : M₁.e = M₂.e)
    (h : ∀ (X) (_ : X ⊆ M₁.e), M₁.R X = M₂.R X) : M₁ = M₂ :=
  eq_of_coe_eq_coe hE
    (eq_of_r_eq_r_forall fun X => by
      rw [← r_eq_coe_r, r_eq_r_inter_ground, ← r_eq_coe_r, r_eq_r_inter_ground X,
        h _ (inter_subset_right _ _), hE])

end Ext

section Dual

/-- The dual of a `matroid_in`. -/
def dual (M : MatroidIn α) : MatroidIn α :=
  equivSubtype.symm (equivSubtype ⟨M, rfl⟩﹡)

instance {α : Type _} : HasMatroidDual (MatroidIn α) :=
  ⟨dual⟩

theorem dual_eq (M : MatroidIn α) : M﹡ = equivSubtype.symm (equivSubtype ⟨M, rfl⟩﹡) :=
  rfl

@[simp]
theorem dual_base_iff : M﹡.base B ↔ M.base (M.e \ B) ∧ B ⊆ M.e :=
  by
  simp_rw [dual_eq, equiv_subtype.symm_base_iff, Matroid.dual.base_iff, equiv_subtype.base_iff,
    coe_mk, and_congr_left_iff, coe_injective.image_compl_eq, image_preimage_eq_inter_range,
    range_coe]
  simp only [diff_inter_self_eq_diff, iff_self_iff, imp_true_iff]

@[simp]
theorem dual_ground (M : MatroidIn α) : M﹡.e = M.e :=
  rfl

@[simp]
theorem dual_dual (M : MatroidIn α) : M﹡﹡ = M := by simp [dual_eq]

theorem dual_inj {M₁ M₂ : MatroidIn α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ := by
  rw [← dual_dual M₁, ← dual_dual M₂, h]

theorem dual_inj_iff {M₁ M₂ : MatroidIn α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ :=
  ⟨dual_inj, congr_arg _⟩

theorem dual_r_cast_eq (M : MatroidIn α) [Finite M.e] {X : Set α} (hX : X ⊆ M.e) :
    (M﹡.R X : ℤ) = X.ncard + M.R (M.e \ X) - M.rk :=
  by
  rw [← @range_coe _ M.E, subset_range_iff_exists_image_eq] at hX
  obtain ⟨X₀, rfl⟩ := hX
  simp_rw [dual_eq, equiv_subtype.symm_r_eq, dual_r_cast_eq, preimage_image_eq _ coe_injective,
    ncard_image_of_injective _ coe_injective, rk_eq_r_ground, rk_def, equiv_subtype.r_eq, coe_mk,
    image_univ, range_coe_subtype, set_of_mem_eq, sub_left_inj, add_right_inj, Nat.cast_inj,
    coe_injective.image_compl_eq, range_coe]

theorem dual_r_add_rk_eq (M : MatroidIn α) [Finite M.e] {X : Set α} (hX : X ⊆ M.e) :
    M﹡.R X + M.rk = X.ncard + M.R (M.e \ X) := by linarith [M.dual_r_cast_eq hX]

@[simp]
theorem dual_indep_iff_coindep : M﹡.indep X ↔ M.Coindep X :=
  by
  simp_rw [indep_iff_subset_base, dual_base_iff, base_iff_coe, coindep,
    Matroid.coindep_iff_disjoint_base]
  constructor
  · rintro ⟨B, ⟨hBc, hBE⟩, hXB⟩
    exact ⟨⟨_, hBc, disjoint_of_subset_left hXB disjoint_sdiff_right⟩, hXB.trans hBE⟩
  rintro ⟨⟨B, hB : M.base B, hdj⟩, hX⟩
  refine' ⟨M.E \ B, ⟨_, diff_subset _ _⟩, subset_diff.mpr ⟨hX, hdj⟩⟩
  rwa [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right_iff_subset.mpr hB.subset_ground]

@[simp]
theorem dual_coindep_iff_indep : M﹡.Coindep X ↔ M.indep X := by
  rw [← dual_dual M, dual_indep_iff_coindep, dual_dual]

@[simp]
theorem dual_circuit_iff_cocircuit : M﹡.Circuit C ↔ M.Cocircuit C :=
  by
  refine'
    (em (C ⊆ M.E)).symm.elim
      (fun hn => iff_of_false (fun hC => hn hC.subset_ground) fun hC => hn hC.subset_ground)
      fun hCE => _
  simp_rw [circuit_iff_mem_minimals, dual_indep_iff_coindep, cocircuit_iff_coe,
    Matroid.cocircuit_iff_mem_minimals, coindep_iff_disjoint_base, not_exists, not_and, ←
    base_iff_coe, dual_ground, subset_diff, not_and, not_disjoint_iff_nonempty_inter, inter_comm]
  exact
    ⟨fun h =>
      ⟨fun B hB => h.1.1 B hB h.1.2, fun D hD h' => h.2 ⟨fun B hB hDE => hD B hB, h'.trans hCE⟩ h'⟩,
      fun h =>
      ⟨⟨fun B hB hCE' => h.1 B hB, hCE⟩, fun D hD hDC =>
        h.2 (fun B hB => hD.1 B hB (hDC.trans hCE)) hDC⟩⟩

@[simp]
theorem dual_cocircuit_iff_circuit : M﹡.Cocircuit C ↔ M.Circuit C := by
  rw [← dual_dual M, dual_circuit_iff_cocircuit, dual_dual]

@[simp]
theorem dual_loop_iff_coloop : M﹡.Loop e ↔ M.Coloop e := by
  rw [coloop, Matroid.coloop_iff_cocircuit, ← cocircuit_iff_coe, ← dual_circuit_iff_cocircuit,
    loop_iff_circuit]

@[simp]
theorem dual_coloop_iff_loop : M﹡.Coloop e ↔ M.Loop e := by
  rw [← dual_dual M, dual_loop_iff_coloop, dual_dual]

theorem coloop_iff_mem_dual_cl_empty : M.Coloop e ↔ e ∈ M﹡.cl ∅ := by
  rw [← dual_dual M, ← dual_loop_iff_coloop, dual_dual, loop_iff_mem_cl_empty]

theorem dual_cl_empty_eq_coloops (M : MatroidIn α) : M﹡.cl ∅ = { e | M.Coloop e } :=
  by
  ext
  rw [← coloop_iff_mem_dual_cl_empty]
  rfl

theorem mem_dual_cl_iff_forall_circuit (he : e ∈ M.e) (hX : X ⊆ M.e) :
    e ∈ M﹡.cl X ↔ ∀ C, M.Circuit C → e ∈ C → (X ∩ C).Nonempty :=
  by
  refine'
    (em (e ∈ X)).elim (fun h => iff_of_true (subset_cl hX h) fun C hC heC => ⟨e, h, heC⟩) fun heX =>
      _
  rw [mem_cl_iff_forall_hyperplane]; swap; assumption; swap; assumption
  refine' ⟨fun h C hC heC => _, fun h H hH hXH => by_contra fun heH => _⟩
  · have con := h (M.E \ C) (cocircuit.compl_hyperplane _)
    · rw [imp_iff_not (fun h => h.2 heC : e ∉ M.E \ C), not_subset_iff_exists_mem_not_mem] at con
      obtain ⟨f, hfX, hfn⟩ := Con
      exact ⟨f, hfX, by_contra fun hf => hfn ⟨hX hfX, hf⟩⟩
    rwa [← dual_circuit_iff_cocircuit, dual_dual]
  have hHC := hH.compl_cocircuit
  rw [dual_cocircuit_iff_circuit, dual_ground] at hHC
  obtain ⟨f, hfX, hf⟩ := h _ hHC ⟨he, heH⟩
  exact hf.2 (hXH hfX)

theorem dual_cl_to_coe (M : MatroidIn α) {X : Set α} (hX : X ⊆ M.e) :
    M﹡.cl X = (M : Matroid α)﹡.cl X :=
  by
  refine'
    Set.ext fun e =>
      (em (e ∈ M.E)).symm.elim (fun he => iff_of_false (not_mem_subset (cl_subset_ground _ _) he) _)
        fun he => _
  · rw [Matroid.mem_dual_cl_iff_forall_circuit]
    refine' fun h => he _
    have con := h _ (loop_coe_of_not_mem_ground he).Circuit (mem_singleton e)
    simp only [inter_singleton_nonempty] at con
    exact hX Con
  simp_rw [mem_dual_cl_iff_forall_circuit he hX, Matroid.mem_dual_cl_iff_forall_circuit, circuit,
    and_imp]
  refine' ⟨fun h C hC heC => h C hC _ heC, fun h C hC _ heC => h C hC heC⟩
  obtain ⟨-, hCE⟩ | ⟨f, hf, rfl⟩ := circuit_coe_iff.mp hC
  exact hCE
  rwa [← mem_singleton_iff.mp heC, singleton_subset_iff]

end Dual

section FlatOfR

/-- A `flat` of rank `k` in `M`. When `k = 0`, the definition excludes infinite-rank flats
  with junk rank `0`.  -/
def FlatOfR (M : MatroidIn α) (k : ℕ) :=
  TransferSetProp (fun γ M' => M'.FlatOfR k) M

theorem flatOfR_zero_iff_loops : M.FlatOfR 0 F ↔ F = M.cl ∅ :=
  by
  simp only [flat_of_r, transfer_set_prop_iff, flat_of_r_zero_iff_loops, equiv_subtype.cl_eq,
    coe_mk, image_empty, preimage_coe_eq_preimage_coe_iff]
  constructor
  · rintro ⟨he, h⟩
    rwa [inter_eq_self_of_subset_left h, inter_eq_self_of_subset_left <| cl_subset_ground _ _] at he
  rintro rfl
  refine' ⟨rfl, cl_subset_ground _ _⟩

-- def flat_of_r (M : matroid_in α) (k : ℕ) (F : set α) :=
theorem flatOfR_iff : M.FlatOfR k F ↔ M.Flat F ∧ M.R F = k ∧ M.RFin F :=
  by
  simp_rw [flat_of_r, transfer_set_prop_iff, Matroid.FlatOfR, flat_eq_transfer_set_prop,
    r_fin_eq_transfer_set_prop]
  simp only [equiv_subtype.flat_iff, coe_mk, image_preimage_coe, equiv_subtype.r_eq,
    equiv_subtype.r_fin_iff, transfer_set_prop_iff, ← r_eq_r_inter_ground]
  tauto

theorem FlatOfR.flat (h : M.FlatOfR k F) : M.Flat F :=
  (flatOfR_iff.mp h).1

theorem FlatOfR.r (h : M.FlatOfR k F) : M.R F = k :=
  (flatOfR_iff.mp h).2.1

theorem FlatOfR.rFin (h : M.FlatOfR k F) : M.RFin F :=
  (flatOfR_iff.mp h).2.2

theorem flatOfR_iff_coe : M.FlatOfR k F ↔ (M : Matroid α).FlatOfR k (F ∪ M.eᶜ) ∧ F ⊆ M.e :=
  by
  rw [flat_of_r_iff, Matroid.FlatOfR, flat, ← r, r_union_compl_ground, r_fin, Iff.comm, ←
    Matroid.rFin_cl_iff, cl_union_eq_cl_of_subset_loops M.compl_ground_subset_loops_coe,
    Matroid.rFin_cl_iff]
  tauto

@[simp]
theorem equivSubtype.flatOfR_iff {E : Set α} {F : Set E} (M : { M : MatroidIn α // M.e = E }) :
    (equivSubtype M).FlatOfR k F ↔ (M : MatroidIn α).FlatOfR k (coe '' F) :=
  by
  obtain ⟨M, rfl⟩ := M
  simp [flat_of_r]

-- @[simp] lemma equiv_subtype.symm_flat_of_r_iff {E F : set α} (M : matroid E) :
--   (equiv_subtype.symm M : matroid_in α).flat_of_r k F ↔ M.flat_of_r k (coe ⁻¹' F) ∧ F ⊆ E  :=
-- by { simp [flat_of_r] }
/-- Flats of rank `k` in `M : matroid_in α` correspond to those in `↑M : matroid α`.-/
def flatOfRCoeEquiv (M : MatroidIn α) (k : ℕ) :
    { F // M.FlatOfR k F } ≃ { F // (M : Matroid α).FlatOfR k F }
    where
  toFun F := ⟨F ∪ M.eᶜ, (flatOfR_iff_coe.mp F.2).1⟩
  invFun F :=
    ⟨F ∩ M.e,
      by
      rw [flat_of_r_iff_coe, and_iff_left (inter_subset_right _ _), union_distrib_right,
        union_compl_self, inter_univ, union_eq_left_iff_subset.mpr]
      · exact F.2
      exact M.compl_ground_subset_loops_coe.trans F.2.Flat.loops_subset⟩
  left_inv := by
    rintro ⟨F, hF⟩
    simp only [coe_mk, inter_distrib_right, compl_inter_self, union_empty,
      inter_eq_self_of_subset_left hF.subset_ground]
  right_inv := by
    rintro ⟨F, hF⟩
    simp only [coe_mk, union_distrib_right, union_compl_self, inter_univ, union_eq_left_iff_subset]
    exact M.compl_ground_subset_loops_coe.trans hF.flat.loops_subset

@[simp]
theorem flatOfRCoeEquiv_apply (F : { F // M.FlatOfR k F }) :
    (M.flatOfRCoeEquiv k F : Set α) = F ∪ M.eᶜ :=
  rfl

@[simp]
theorem flatOfRCoeEquiv_apply_symm (F : { F // (M : Matroid α).FlatOfR k F }) :
    ((M.flatOfRCoeEquiv k).symm F : Set α) = F ∩ M.e :=
  rfl

/-- A `point` is a rank-one flat -/
def Point (M : MatroidIn α) (P : Set α) :=
  M.FlatOfR 1 P

/-- A `line` is a rank-two flat -/
def Line (M : MatroidIn α) (L : Set α) :=
  M.FlatOfR 2 L

theorem point_eq_transferSetProp (M : MatroidIn α) :
    M.Point = TransferSetProp (fun _ => Matroid.Point) M :=
  rfl

theorem line_eq_transferSetProp (M : MatroidIn α) :
    M.line = TransferSetProp (fun _ => Matroid.Line) M :=
  rfl

theorem sum_ncard_point_diff_loops (M : MatroidIn α) [Finite M.e] :
    (∑ᶠ P : { P // M.Point P }, ((P : Set α) \ M.cl ∅).ncard) = (M.e \ M.cl ∅).ncard :=
  by
  set e := transfer_set_prop_equiv (fun _ => Matroid.Point) M
  convert(@finsum_comp_equiv _ _ _ _ e.symm _).symm
  convert(equiv_subtype ⟨M, rfl⟩).sum_ncard_point_diff_loops.symm using 1
  · simp only [equiv_subtype.cl_eq, coe_mk, image_empty]
    rw [← ncard_image_of_injective _ coe_injective, image_compl_preimage, range_coe]
  apply finsum_congr
  rintro ⟨P, hP⟩
  simp only [transfer_set_prop_equiv_apply_symm, coe_mk, equiv_subtype.cl_eq, image_empty]
  rw [← ncard_image_of_injective _ coe_injective, image_diff coe_injective, image_preimage_coe,
    inter_eq_self_of_subset_left (cl_subset_ground _ _)]

noncomputable def numPoints (M : MatroidIn α) : ℕ :=
  Nat.card { P // M.Point P }

theorem numPoints_eq_equivSubtype (M : MatroidIn α) :
    M.numPoints = (equivSubtype ⟨M, rfl⟩).numPoints :=
  Nat.card_eq_of_bijective _ (transferSetPropEquiv (fun _ => Matroid.Point) M).Bijective

theorem numPoints_eq_coe (M : MatroidIn α) : M.numPoints = (M : Matroid α).numPoints :=
  Nat.card_eq_of_bijective (M.flatOfRCoeEquiv 1) (Equiv.bijective _)

theorem simple_iff_numPoints_eq_card [Finite M.e] (hnl : ¬M.base ∅) :
    M.simple ↔ M.numPoints = M.e.ncard :=
  by
  nth_rw 1 [← eq_image_symm_image_equiv_subtype M]
  rw [equiv_subtype.symm_simple_iff, Matroid.simple_iff_numPoints_eq_card, ←
    num_points_eq_equiv_subtype, ncard_univ, nat.card_coe_set_eq]
  simpa

end FlatOfR

end MatroidIn

