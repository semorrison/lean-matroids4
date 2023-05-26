import Mathlib.Data.Set.Basic

variable {α : Type _} {s : Set α} {a : α}

namespace Set

theorem singleton_inter_eq_of_mem {x : α} (hx : x ∈ s) : {x} ∩ s = {x} :=
  (inter_subset_left _ _).antisymm (subset_inter subset_rfl (singleton_subset_iff.mpr hx))

theorem inter_singleton_eq_of_mem {α : Type _} {x : α} {s : Set α} (hx : x ∈ s) : s ∩ {x} = {x} :=
  (inter_subset_right _ _).antisymm (subset_inter (singleton_subset_iff.mpr hx) subset_rfl)

@[simp]
theorem not_mem_diff_singleton {α : Type _} (x : α) (s : Set α) : x ∉ s \ {x} :=
  not_mem_diff_of_mem <| mem_singleton _

theorem sSubset_iff_subset_diff_singleton {α : Type _} {s t : Set α} :
    s ⊂ t ↔ ∃ x ∈ t, s ⊆ t \ {x} := by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨x, hxt, hxs⟩ := exists_of_ssubset h
    refine' ⟨x, hxt, subset_diff_singleton h.subset hxs⟩
  rintro ⟨x, hxt, hs⟩
  exact hs.trans_ssubset (diff_singleton_ssubset.mpr hxt)

theorem hasSubset.Subset.sSubset_of_nonempty_diff {α : Type _} {s t : Set α} (hst : s ⊆ t)
    (he : (t \ s).Nonempty) : s ⊂ t :=
  hst.ssubset_of_ne
    (by
      rintro rfl
      simpa using he)

theorem inter_subset_union (s t : Set α) : s ∩ t ⊆ s ∪ t :=
  (inter_subset_left _ _).trans (subset_union_left _ _)

theorem union_diff_cancel_of_subset {s s' : Set α} (t : Set α) (h : s' ⊆ s) : s ∪ t \ s' = s ∪ t :=
  by rw [← union_eq_self_of_subset_right h, union_assoc, union_diff_self, union_assoc]

@[simp]
theorem symmDiff_univ (s : Set α) : s ∆ univ = sᶜ :=
  symmDiff_top s

end Set

