import Matroid.Rank
import Project.Mathlib.Data.Set.Image

noncomputable section

open Classical

open Set

namespace Matroid

universe u

section Iso

variable {E E₀ E₁ E₂ : Type u} {M₀ : Matroid E₀} {M₁ : Matroid E₁} {M₂ : Matroid E₂}

/-- Two matroids are isomorphic if there is a map between ground sets that preserves bases -/
def IsIso (M₁ : Matroid E₁) (M₂ : Matroid E₂) (e : E₁ ≃ E₂) :=
  ∀ B, M₁.base B ↔ M₂.base (e '' B)

/-- A bundled isomorphism between two matroids -/
structure Iso (M₁ : Matroid E₁) (M₂ : Matroid E₂) where
  toFun : E₁ ≃ E₂
  on_base : ∀ B, M₁.base B ↔ M₂.base (to_fun '' B)

-- mathport name: «expr ≃i »
infixl:75 " ≃i " => Matroid.Iso

instance : CoeFun (M₁ ≃i M₂) fun _ => E₁ → E₂ :=
  ⟨fun e => e.toFun⟩

def Iso.refl (M : Matroid E) : M ≃i M :=
  ⟨Equiv.refl E, fun B => by simp⟩

def Iso.symm (e : M₁ ≃i M₂) : M₂ ≃i M₁ :=
  ⟨e.toFun.symm, fun B => by
    rw [e.on_base]
    simp⟩

end Iso

section Embed

variable {E E' : Type u} {M : Matroid E} {M' : Matroid E'} {f : E ↪ E'}

/-- Embed a matroid as a restriction in a larger type. All elements outside the image are loops. -/
def image (M : Matroid E) (f : E ↪ E') : Matroid E' :=
  matroidOfIndep (fun I' => ∃ I, M.indep I ∧ f '' I = I') ⟨_, M.empty_indep, by simp⟩
    (by
      rintro _ _ ⟨J, hJ, rfl⟩ hIJ; refine' ⟨J ∩ f ⁻¹' I, hJ.subset (inter_subset_left _ _), _⟩
      rw [image_inter f.injective, image_preimage_eq_inter_range, ← inter_assoc,
        inter_eq_right_iff_subset.mpr hIJ, eq_comm,
        inter_eq_left_iff_subset.mpr (hIJ.trans (image_subset_range _ _))])
    (by
      rintro _ _ ⟨I, hI, rfl⟩ hIn ⟨⟨B, hB, rfl⟩, hBmax⟩
      obtain ⟨e, he, heI⟩ := hI.exists_insert_of_not_base _ (hB.base_of_maximal fun J hJ hBJ => _)
      ·
        exact
          ⟨f e, by rwa [← image_diff f.injective, f.injective.mem_set_image],
            ⟨_, heI, image_insert_eq⟩⟩
      · refine' fun hI' => hIn ⟨⟨_, hI, rfl⟩, _⟩
        rintro _ ⟨J, hJ, rfl⟩ hIJ
        rw [hI'.eq_of_subset_indep hJ]
        rwa [image_subset_image_iff f.injective] at hIJ
      exact
        hBJ.antisymm
          ((image_subset_image_iff f.injective).mp (hBmax ⟨_, hJ, rfl⟩ (image_subset _ hBJ))))
    (by
      rintro _ X ⟨I, hI, rfl⟩ hIX
      obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (image_subset_iff.mp hIX)
      refine' ⟨f '' J, ⟨⟨_, hJ.indep, rfl⟩, image_subset _ hIJ, image_subset_iff.mpr hJ.subset⟩, _⟩
      rintro _ ⟨⟨K, hK, rfl⟩, hIK, hKX⟩ hJK
      rw [hJ.eq_of_subset_indep hK ((image_subset_image_iff f.injective).mp hJK)
          (image_subset_iff.mp hKX)])

theorem image.setOf_indep_eq (M : Matroid E) :
    { I | (M.image f).indep I } = Set.image f '' { I | M.indep I } :=
  by
  ext
  simp_rw [image, matroid_of_indep_apply]
  rfl

@[simp]
theorem image.indep_iff {I' : Set E'} : (M.image f).indep I' ↔ ∃ I, M.indep I ∧ f '' I = I' := by
  simp [image]

theorem image.compl_range_subset_loops (M : Matroid E) (f : E ↪ E') : range fᶜ ⊆ (M.image f).cl ∅ :=
  by
  refine' fun e he => loop_iff_mem_cl_empty.mp _
  simp_rw [loop_iff_dep, image.indep_iff, not_exists, not_and, f.injective.image_eq_singleton_iff,
    not_exists, not_and]
  rintro I hI e rfl rfl
  simpa using he

@[simp]
theorem image.base_iff {B' : Set E'} : (M.image f).base B' ↔ ∃ B, M.base B ∧ B' = f '' B :=
  by
  simp_rw [base_iff_maximal_indep, image.indep_iff]
  constructor
  · rintro ⟨⟨B, hB, rfl⟩, h⟩
    exact
      ⟨B,
        ⟨hB, fun I hI hBI =>
          (image_eq_image f.injective).mp (h _ ⟨I, hI, rfl⟩ (image_subset f hBI))⟩,
        rfl⟩
  rintro ⟨B, ⟨hBi, hB⟩, rfl⟩
  refine' ⟨⟨_, hBi, rfl⟩, _⟩
  rintro _ ⟨I, hI, rfl⟩ hBI
  rw [hB _ hI <| (image_subset_image_iff f.injective).mp hBI]

@[simp]
theorem image.basis_iff {I' X' : Set E'} :
    (M.image f).Basis I' X' ↔ ∃ I, M.Basis I (f ⁻¹' X') ∧ I' = f '' I :=
  by
  simp_rw [basis_iff, image.indep_iff]
  constructor
  · rintro ⟨⟨I, hI, rfl⟩, hIX', hmax⟩
    refine'
      ⟨I, ⟨hI, image_subset_iff.mp hIX', fun J hJ hIJ hJX => (image_eq_image f.injective).mp _⟩,
        rfl⟩
    rw [hmax _ ⟨_, hJ, rfl⟩ (image_subset _ hIJ) (image_subset_iff.mpr hJX)]
  rintro ⟨I, ⟨hI, hIX, hmax⟩, rfl⟩
  refine' ⟨⟨_, hI, rfl⟩, image_subset_iff.mpr hIX, _⟩
  rintro _ ⟨J, hJ, rfl⟩ hIJ hJX
  rw [hmax _ hJ ((image_subset_image_iff f.injective).mp hIJ) (image_subset_iff.mp hJX)]

@[simp]
theorem image.circuit_iff {C' : Set E'} :
    (M.image f).Circuit C' ↔ (∃ C, M.Circuit C ∧ C' = f '' C) ∨ ∃ e ∈ range fᶜ, C' = {e} :=
  by
  simp_rw [circuit_iff, image.indep_iff, not_exists, not_and]
  constructor
  · rintro ⟨h, h'⟩
    obtain hC' | hC' := em (C' ⊆ range f)
    · obtain ⟨C, rfl⟩ := subset_range_iff_exists_image_eq.mp hC'
      refine'
        Or.inl ⟨C, ⟨fun hi => h _ hi rfl, fun I hd hIC => (image_eq_image f.injective).mp _⟩, rfl⟩
      refine' h' _ (fun I' hI' hf => hd _) (image_subset _ hIC)
      rwa [← (image_eq_image f.injective).mp hf]
    obtain ⟨e, heC, her⟩ := not_subset.mp hC'
    refine' Or.inr ⟨e, her, (h' {e} (fun I hI heI => her _) (singleton_subset_iff.mpr heC)).symm⟩
    exact (image_subset_range _ _) (heI.symm.subset (mem_singleton e))
  rintro (⟨C, ⟨hC, hmin⟩, rfl⟩ | ⟨e, he, rfl⟩)
  · refine'
      ⟨fun I hI h_eq => hC (by rwa [← (image_eq_image f.injective).mp h_eq]), fun C' hC' hC'C => _⟩
    obtain ⟨C₀, rfl⟩ := subset_range_iff_exists_image_eq.mp (hC'C.trans (image_subset_range _ _))
    refine' hC'C.antisymm (image_subset_iff.mpr _)
    rw [preimage_image_eq _ f.injective, ←
      hmin _ (fun hi => hC' _ hi rfl) ((image_subset_image_iff f.injective).mp hC'C)]
  exact
    ⟨fun I hI h' => he (singleton_subset_iff.mp (h'.symm.subset.trans (image_subset_range _ _))),
      fun I h h' =>
      (subset_singleton_iff_eq.mp h').elim
        (fun h' => (h ∅ M.empty_indep (by rwa [eq_comm, image_empty])).elim) id⟩

@[simp]
theorem image.cl_eq (M : Matroid E) (f : E ↪ E') (X' : Set E') :
    (M.image f).cl X' = f '' M.cl (f ⁻¹' X') ∪ range fᶜ :=
  by
  obtain ⟨I', hI'⟩ := (M.image f).exists_basis X'
  obtain ⟨I, hI, rfl⟩ := image.basis_iff.mp hI'
  ext e
  simp only [mem_union, mem_image, mem_compl_iff, mem_range, not_exists]
  obtain ⟨e, rfl⟩ | he := em (e ∈ range f)
  · have hfalse : ¬∀ x, ¬f x = f e := fun h => h e rfl
    rw [iff_false_intro hfalse, or_false_iff]
    simp only [EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
    obtain he | he := em (f e ∈ X')
    · exact iff_of_true (mem_cl_of_mem _ he) (mem_cl_of_mem _ he)
    simp_rw [hI.mem_cl_iff_of_not_mem he, hI'.mem_cl_iff_of_not_mem he, image.indep_iff, ←
      image_insert_eq, image_eq_image f.injective, exists_eq_right]
  refine' iff_of_true (loop.mem_cl _ _) (Or.inr _)
  · simp_rw [loop_iff_dep, image.indep_iff, not_exists, not_and]
    exact fun x hx hex => he ((image_subset_range f x) (hex.symm.subset (mem_singleton e)))
  rintro x rfl
  exact he (mem_range_self _)

@[simp]
theorem image.flat_iff {F' : Set E'} :
    (M.image f).Flat F' ↔ ∃ F, M.Flat F ∧ F' = f '' F ∪ range fᶜ :=
  by
  rw [flat_iff_cl_self, image.cl_eq]
  refine' ⟨fun h => _, _⟩
  · refine' ⟨f ⁻¹' F', _⟩
    suffices hflat : M.flat (f ⁻¹' F')
    · convert And.intro hflat h.symm
      rw [hflat.cl]
    rw [← h, preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      preimage_image_eq _ f.injective]
    exact M.flat_of_cl _
  rintro ⟨F, hF, rfl⟩
  rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
    preimage_image_eq _ f.injective, hF.cl]

theorem image.hyperplane_iff {H' : Set E'} :
    (M.image f).Hyperplane H' ↔ ∃ H, M.Hyperplane H ∧ H' = f '' H ∪ range fᶜ :=
  by
  simp_rw [hyperplane_iff_maximal_proper_flat, image.flat_iff]
  constructor
  · rintro ⟨⟨H, hfH, rfl⟩, hss, h⟩
    refine' ⟨_, ⟨hfH, ssubset_univ_iff.mpr _, fun F hHF hF => eq_univ_of_forall fun e => _⟩, rfl⟩
    · rintro rfl
      rw [image_univ, union_compl_self] at hss
      exact hss.ne rfl
    simpa using (h (f '' F ∪ range fᶜ) _ ⟨F, hF, rfl⟩).symm.Subset (mem_univ (f e))
    rw [ssubset_iff_of_subset (union_subset_union_left _ (image_subset _ hHF.subset))]
    obtain ⟨x, hxH, hxF⟩ := exists_of_ssubset hHF
    refine' ⟨f x, Or.inl (mem_image_of_mem _ hxH), _⟩
    rwa [mem_union, f.injective.mem_set_image, not_or, not_mem_compl_iff,
      iff_true_intro (mem_range_self _), and_true_iff]
  rintro ⟨H, ⟨⟨hfH, hHss, hH⟩, rfl⟩⟩
  refine' ⟨⟨H, hfH, rfl⟩, ssubset_univ_iff.mpr fun hu => hHss.ne (eq_univ_of_forall fun e => _), _⟩
  · simpa using hu.symm.subset (mem_univ (f e))
  rintro X hHX ⟨F, hF, rfl⟩
  rw [hH F _ hF, image_univ, union_compl_self]
  refine'
    ssubset_of_ne_of_subset
      (by
        rintro rfl
        exact hHX.ne rfl)
      fun e heH => _
  have hss := hHX.subset
  simpa using hss (Or.inl (mem_image_of_mem f heH))

theorem image.cocircuit_iff {K' : Set E'} :
    (M.image f).Cocircuit K' ↔ ∃ K, M.Cocircuit K ∧ K' = f '' K :=
  by
  simp_rw [← compl_hyperplane_iff_cocircuit, image.hyperplane_iff]
  refine' ⟨Exists.imp' compl _, Exists.imp' compl _⟩
  ·
    simp_rw [@compl_eq_comm _ K', compl_union, compl_compl, f.injective.compl_image_eq,
      inter_distrib_right, compl_inter_self, union_empty,
      inter_eq_self_of_subset_left (image_subset_range _ _), eq_comm, iff_true_intro id,
      imp_true_iff]
  simp_rw [@compl_eq_comm _ K', compl_union, f.injective.compl_image_eq, compl_compl,
    inter_distrib_right, compl_inter_self, union_empty,
    inter_eq_self_of_subset_left (image_subset_range _ _), eq_comm, iff_true_intro id, imp_true_iff]

@[simp]
theorem image.r_eq (M : Matroid E) (X' : Set E') : (M.image f).R X' = M.R (f ⁻¹' X') :=
  by
  obtain ⟨I, hI⟩ := (M.image f).exists_basis X'
  obtain ⟨I₀, hI₀, rfl⟩ := image.basis_iff.mp hI
  rw [← hI.card, ncard_image_of_injective _ f.injective, ← hI₀.card]

@[simp]
theorem image.loop_iff {e' : E'} :
    (M.image f).Loop e' ↔ (∃ e, M.Loop e ∧ e' = f e) ∨ e' ∈ range fᶜ :=
  by
  simp_rw [loop_iff_circuit, image.circuit_iff, @eq_comm _ {e'}, f.injective.image_eq_singleton_iff,
    mem_compl_iff, mem_range, not_exists, singleton_eq_singleton_iff, exists_prop, exists_eq_right]
  constructor
  · rintro (⟨C, hC, a, rfl, rfl⟩ | h)
    exact Or.inl ⟨_, hC, rfl⟩
    exact Or.inr h
  rintro (⟨e, he, rfl⟩ | h); exact Or.inl ⟨_, he, ⟨_, rfl, rfl⟩⟩; exact Or.inr h

@[simp]
theorem image.nonloop_iff {e' : E'} : (M.image f).Nonloop e' ↔ ∃ e, M.Nonloop e ∧ e' = f e :=
  by
  simp_rw [← not_loop_iff, image.loop_iff, not_or, not_exists, not_and, not_mem_compl_iff]
  constructor
  · rintro ⟨h, ⟨e, rfl⟩⟩
    exact ⟨_, fun h' => h _ h' rfl, rfl⟩
  rintro ⟨e, he, rfl⟩; exact ⟨fun h h' h_eq => he (by rwa [f.injective h_eq]), mem_range_self _⟩

@[simp]
theorem image.trans {E₀ E₁ E₂ : Type _} {M₀ : Matroid E₀} {f₀ : E₀ ↪ E₁} {f₁ : E₁ ↪ E₂} :
    (M₀.image f₀).image f₁ = M₀.image (f₀.trans f₁) :=
  by
  refine' eq_of_indep_iff_indep_forall fun I₂ => _
  simp only [image.indep_iff, Function.Embedding.trans_apply]
  constructor
  · rintro ⟨I₁, ⟨⟨I₀, hI₀, rfl⟩, rfl⟩⟩
    exact
      ⟨I₀, hI₀, by
        ext
        simp⟩
  rintro ⟨I₀, hI₀, rfl⟩;
  exact
    ⟨f₀ '' I₀, ⟨I₀, hI₀, rfl⟩, by
      ext
      simp⟩

/-- A matroid on `E'` and an injection from `E` into `E'` gives rise to a matroid on `E` -/
def preimage {E E' : Type u} (M' : Matroid E') (f : E ↪ E') : Matroid E :=
  matroidOfIndep (fun I => M'.indep (f '' I)) (by simp)
    (fun I J hJ hIJ => hJ.Subset (image_subset _ hIJ))
    (by
      intro I B hI hIn hB
      obtain ⟨e, ⟨⟨e, he, rfl⟩, he'⟩, hi⟩ :=
        @indep.exists_insert_of_not_basis _ _ (f '' B) (range f) _ hI (image_subset_range _ _) _ _
      · rw [f.injective.mem_set_image] at he'
        rw [← image_insert_eq] at hi
        exact ⟨e, ⟨he, he'⟩, hi⟩
      · refine' fun hI' => hIn ⟨hI, fun J hJ hIJ => ((image_eq_image f.injective).mp _).Subset⟩
        exact (hI'.eq_of_subset_indep hJ (image_subset _ hIJ) (image_subset_range _ _)).symm
      refine' hB.1.basis_of_maximal_subset (image_subset_range _ _) fun J hJ hBJ hJr => _
      obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.mp hJr
      exact image_subset _ (hB.2 hJ ((image_subset_image_iff f.injective).mp hBJ)))
    (by
      intro I X hI hIX
      obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (image_subset _ hIX)
      obtain ⟨J, rfl⟩ :=
        subset_range_iff_exists_image_eq.mp (hJ.subset.trans (image_subset_range _ _))
      refine'
        ⟨J,
          ⟨hJ.indep, (image_subset_image_iff f.injective).mp hIJ,
            (image_subset_image_iff f.injective).mp hJ.subset⟩,
          fun K hK hJK =>
          (image_subset_image_iff f.injective).mp
            (hJ.2 ⟨hK.1, image_subset _ hK.2.2⟩ (image_subset _ hJK))⟩)

@[simp]
theorem preimage.indep_iff {I : Set E} : (M'.Preimage f).indep I ↔ M'.indep (f '' I) := by
  simp [preimage]

@[simp]
theorem preimage.setOf_indep_eq (M' : Matroid E') :
    { I | (M'.Preimage f).indep I } = { I | M'.indep (Set.image f I) } :=
  by
  ext
  simp

@[simp]
theorem preimage.basis_iff {I X : Set E} : (M'.Preimage f).Basis I X ↔ M'.Basis (f '' I) (f '' X) :=
  by
  simp_rw [basis_iff, preimage.indep_iff, and_congr_right_iff, image_subset_image_iff f.injective,
    and_congr_right_iff]
  refine' fun hI hIX => ⟨fun h J hJ hIJ hJX => _, fun h J hJ hIJ hJX => _⟩
  · obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.mp (hJX.trans (image_subset_range _ _))
    rw [h _ hJ ((image_subset_image_iff f.injective).mp hIJ)
        ((image_subset_image_iff f.injective).mp hJX)]
  rw [← image_eq_image f.injective, h _ hJ (image_subset _ hIJ) (image_subset _ hJX)]

@[simp]
theorem preimage.base_iff {B : Set E} : (M'.Preimage f).base B ↔ M'.Basis (f '' B) (range f) := by
  rw [base_iff_basis_univ, preimage.basis_iff, image_univ]

@[simp]
theorem preimage.cl_eq (M' : Matroid E') (f : E ↪ E') (X : Set E) :
    (M'.Preimage f).cl X = f ⁻¹' M'.cl (f '' X) :=
  by
  rw [Set.ext_iff]
  refine' fun e =>
    (em (e ∈ X)).elim
      (fun heX => iff_of_true (mem_cl_of_mem _ heX) (M'.mem_cl_of_mem ⟨_, heX, rfl⟩)) fun heX => _
  obtain ⟨I, hI⟩ := (M'.preimage f).exists_basis X
  have hb := preimage.basis_iff.mp hI
  rw [← hI.cl, hI.indep.mem_cl_iff_of_not_mem (not_mem_subset hI.subset heX), preimage.indep_iff, ←
    hb.cl, mem_preimage, hb.indep.mem_cl_iff_of_not_mem _, image_insert_eq]
  rw [f.injective.mem_set_image]
  exact not_mem_subset hI.subset heX

@[simp]
theorem preimage.flat_iff {F : Set E} :
    (M'.Preimage f).Flat F ↔ M'.cl (f '' F) ∩ range f = f '' F := by
  rw [flat_iff_cl_self, preimage.cl_eq, ← image_eq_image f.injective, image_preimage_eq_inter_range]

@[simp]
theorem preimage.circuit_iff {C : Set E} : (M'.Preimage f).Circuit C ↔ M'.Circuit (f '' C) :=
  by
  simp_rw [circuit_iff, preimage.indep_iff, and_congr_right_iff]
  refine' fun hd => ⟨fun h I hI hIC => _, fun h I hI hIC => _⟩
  · obtain ⟨I, rfl⟩ := subset_range_iff_exists_image_eq.mp (hIC.trans (image_subset_range _ _))
    rw [h _ hI ((image_subset_image_iff f.injective).mp hIC)]
  exact (image_eq_image f.injective).mp (h _ hI ((image_subset_image_iff f.injective).mpr hIC))

@[simp]
theorem preimage.r_eq (M' : Matroid E') (X : Set E) : (M'.Preimage f).R X = M'.R (f '' X) :=
  by
  obtain ⟨I, hI⟩ := (M'.preimage f).exists_basis X
  rw [← hI.card, ← (preimage.basis_iff.mp hI).card, ncard_image_of_injective _ f.injective]

@[simp]
theorem preimage.nonloop_iff {e : E} : (M'.Preimage f).Nonloop e ↔ M'.Nonloop (f e) := by
  rw [← indep_singleton, ← indep_singleton, preimage.indep_iff, image_singleton]

@[simp]
theorem preimage.loop_iff {e : E} : (M'.Preimage f).Loop e ↔ M'.Loop (f e) := by
  rw [← not_iff_not, not_loop_iff, not_loop_iff, preimage.nonloop_iff]

@[simp]
theorem preimage_image (M : Matroid E) (f : E ↪ E') : (M.image f).Preimage f = M :=
  by
  simp_rw [eq_iff_indep_iff_indep_forall, preimage.indep_iff, image.indep_iff]
  refine' fun I => ⟨_, fun h => ⟨_, h, rfl⟩⟩
  rintro ⟨I₀, hI₀, hf⟩; rwa [← (image_eq_image f.injective).mp hf]

theorem image_preimage_eq_of_forall_subset_range (M' : Matroid E') (f : E ↪ E')
    (h : ∀ I', M'.indep I' → I' ⊆ range f) : (M'.Preimage f).image f = M' :=
  by
  simp_rw [eq_iff_indep_iff_indep_forall, image.indep_iff, preimage.indep_iff]
  refine' fun I' => ⟨_, fun h' => _⟩
  · rintro ⟨I, hI, rfl⟩
    exact hI
  obtain ⟨I, rfl⟩ := subset_range_iff_exists_image_eq.mp (h I' h')
  exact ⟨_, h', rfl⟩

@[simp]
theorem preimage.trans {E₀ E₁ E₂ : Type _} {M₂ : Matroid E₂} {f₀ : E₀ ↪ E₁} {f₁ : E₁ ↪ E₂} :
    (M₂.Preimage f₁).Preimage f₀ = M₂.Preimage (f₀.trans f₁) := by
  simp_rw [eq_iff_indep_iff_indep_forall, preimage.indep_iff, image_image,
    Function.Embedding.trans_apply, iff_self_iff, forall_const]

end Embed

section congr

variable {E E₀ E₁ E₂ : Type u} {e : E₁ ≃ E₂} {M₀ : Matroid E₀} {M₁ : Matroid E₁} {M₂ : Matroid E₂}

/-- An equivalence between types induces a map from a matroid on one type to one on another -/
def congr (M₁ : Matroid E₁) (e : E₁ ≃ E₂) : Matroid E₂ :=
  M₁.Preimage e.symm.toEmbedding

@[simp]
theorem congr_eq_preimage (M₁ : Matroid E₁) (e : E₁ ≃ E₂) :
    M₁.congr e = M₁.Preimage e.symm.toEmbedding :=
  rfl

theorem congr_eq_image (M₁ : Matroid E₁) (e : E₁ ≃ E₂) : M₁.congr e = M₁.image e.toEmbedding :=
  by
  simp_rw [eq_iff_indep_iff_indep_forall, congr_eq_preimage, image.indep_iff, preimage.indep_iff]
  exact fun I =>
    ⟨fun h =>
      ⟨e.symm '' I, h, by
        ext
        simp⟩,
      by
      rintro ⟨I, hI, rfl⟩
      convert hI
      ext
      simp⟩

theorem congr.indep_iff {I : Set E₂} : (M₁.congr e).indep I ↔ M₁.indep (e.symm '' I) := by simp

theorem congr.symm_indep_iff {I : Set E₁} : (M₂.congr e.symm).indep I ↔ M₂.indep (e '' I) := by simp

@[simp]
theorem congr.base_iff {B : Set E₂} : (M₁.congr e).base B ↔ M₁.base (e.symm '' B) := by
  simp [← base_iff_basis_univ]

@[simp]
theorem congr.symm_base_iff {B : Set E₁} : (M₂.congr e.symm).base B ↔ M₂.base (e '' B) := by
  simp [base_iff_basis_univ]

theorem congr.basis_iff {I X : Set E₂} :
    (M₁.congr e).Basis I X ↔ M₁.Basis (e.symm '' I) (e.symm '' X) := by simp

theorem congr.symm_basis_iff {e : E₁ ≃ E₂} {M₂ : Matroid E₂} {I X : Set E₁} :
    (M₂.congr e.symm).Basis I X ↔ M₂.Basis (e '' I) (e '' X) := by simp

theorem congr.r_eq (e : E₁ ≃ E₂) (M₁ : Matroid E₁) (X : Set E₂) :
    (M₁.congr e).R X = M₁.R (e.symm '' X) := by simp

theorem congr.symm_r_eq (e : E₁ ≃ E₂) (M₂ : Matroid E₂) (X : Set E₁) :
    (M₂.congr e.symm).R X = M₂.R (e '' X) := by simp

theorem congr.circuit_iff {C : Set E₂} : (M₁.congr e).Circuit C ↔ M₁.Circuit (e.symm '' C) := by
  simp

theorem congr.symm_circuit_iff {C : Set E₁} : (M₂.congr e.symm).Circuit C = M₂.Circuit (e '' C) :=
  by simp

@[simp]
theorem congr.flat_iff {F : Set E₂} : (M₁.congr e).Flat F ↔ M₁.Flat (e.symm '' F) := by
  rw [congr_eq_preimage, preimage.flat_iff, Equiv.coe_toEmbedding, Equiv.range_eq_univ, inter_univ,
    ← flat_iff_cl_self]

@[simp]
theorem congr.symm_flat_iff {F : Set E₁} : (M₂.congr e.symm).Flat F = M₂.Flat (e '' F) := by
  simp [← flat_iff_cl_self]

theorem congr.loop_iff {x : E₂} : (M₁.congr e).Loop x ↔ M₁.Loop (e.symm x) := by simp

theorem congr.symm_loop_iff {x : E₁} : (M₂.congr e.symm).Loop x ↔ M₂.Loop (e x) := by simp

theorem congr.nonloop_iff {x : E₂} : (M₁.congr e).Nonloop x ↔ M₁.Nonloop (e.symm x) := by simp

theorem congr.symm_nonloop_iff {x : E₁} : (M₂.congr e.symm).Nonloop x ↔ M₂.Nonloop (e x) := by simp

end congr

end Matroid

