import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Minimal

variable {α β : Type _}

namespace Set

theorem Finite.exists_minimal_wrt [PartialOrder β] (f : α → β) {s : Set α} (h : s.Finite) :
    s.Nonempty → ∃ (a : α)(H : a ∈ s), ∀ a' : α, a' ∈ s → f a' ≤ f a → f a = f a' :=
  @Set.Finite.exists_maximal_wrt α (OrderDual β) _ f s h

theorem Finite.exists_maximal [Finite α] [PartialOrder α] (P : α → Prop) (h : ∃ x, P x) :
    ∃ m, P m ∧ ∀ x, P x → m ≤ x → m = x :=
  by
  obtain ⟨m, hm, hm'⟩ := finite.exists_maximal_wrt (@id α) (setOf P) (to_finite _) h
  exact ⟨m, hm, hm'⟩

theorem Finite.exists_minimal [Finite α] [PartialOrder α] (P : α → Prop) (h : ∃ x, P x) :
    ∃ m, P m ∧ ∀ x, P x → x ≤ m → m = x :=
  @Finite.exists_maximal (OrderDual α) _ _ P h

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t' «expr ⊂ » t) -/
theorem Finite.exists_minimal_subset {s : Set α} {P : Set α → Prop} (hs : s.Finite) (hsP : P s) :
    ∃ (t : _)(_ : t ⊆ s), P t ∧ ∀ (t') (_ : t' ⊂ t), ¬P t' :=
  by
  haveI := hs.to_subtype
  obtain ⟨t₀, ht₀, ht₀min⟩ := finite.exists_minimal (P ∘ Set.image (coe : s → α)) ⟨univ, by simpa⟩
  refine' ⟨coe '' t₀, by simp, ht₀, fun t' ht' hPt' => ht'.Ne _⟩
  have ht's : t' ⊆ s := ht'.subset.trans (by simp)
  have ht'' := Subtype.coe_image_of_subset ht's
  simp_rw [Function.comp_apply] at ht₀ ht₀min
  rw [ht₀min { x : s | ↑x ∈ t' } (by rwa [ht'']), ht'']
  convert@preimage_mono _ _ (coe : s → α) _ _ ht'.subset
  rw [preimage_image_eq _ Subtype.coe_injective]

theorem Finite.maximals_nonempty_of_exists {s : Set α} (hs : s.Finite) (P : Set α → Prop)
    {s₀ : Set α} (hs₀s : s₀ ⊆ s) (hs₀ : P s₀) : (maximals (· ⊆ ·) { t | t ⊆ s ∧ P t }).Nonempty :=
  by
  haveI := hs.to_subtype
  obtain ⟨t, ht⟩ :=
    finite.exists_maximal (P ∘ Set.image (coe : s → α))
      ⟨coe ⁻¹' s₀, by
        rwa [Function.comp_apply, Subtype.image_preimage_coe, inter_eq_self_of_subset_left hs₀s]⟩
  simp only [Function.comp_apply, le_eq_subset] at ht
  refine'
    ⟨coe '' t, ⟨(image_subset_range _ _).trans_eq Subtype.range_coe, ht.1⟩, fun t' ht' htt' => _⟩
  obtain ⟨t', rfl⟩ := subset_range_iff_exists_image_eq.mp (ht'.1.trans_eq subtype.range_coe.symm)
  rw [ht.2 t' ht'.2 ((image_subset_image_iff Subtype.coe_injective).mp htt')]

/-- This seems a strict improvement over the nonprimed version in mathlib - only the image
needs to be finite, not the set itself.  -/
theorem Finite.exists_maximal_wrt' {α β : Type _} [PartialOrder β] (f : α → β) (s : Set α)
    (h : (f '' s).Finite) (h₀ : s.Nonempty) :
    ∃ (a : α)(H : a ∈ s), ∀ a' : α, a' ∈ s → f a ≤ f a' → f a = f a' :=
  by
  obtain ⟨_, ⟨a, ha, rfl⟩, hmax⟩ := finite.exists_maximal_wrt id (f '' s) h (h₀.image f)
  exact ⟨a, ha, fun a' ha' hf => hmax _ (mem_image_of_mem f ha') hf⟩

/-- Is this somewhere in mathlib? Can't find it-/
theorem Nat.finite_iff_exists_ub {s : Set ℕ} : s.Finite ↔ ∃ m, ∀ x ∈ s, x ≤ m :=
  by
  refine'
    ⟨fun h => (eq_empty_or_nonempty s).elim (fun he => ⟨0, by simp [he]⟩) fun hs => _,
      fun ⟨m, hm⟩ => { x | x ≤ m }.toFinite.Subset hm⟩
  refine' (finite.exists_maximal_wrt id s h hs).imp fun m hm x hxs => le_of_not_lt fun hlt => _
  obtain ⟨-, h⟩ := hm
  exact hlt.ne (h x hxs hlt.le)

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t₀ «expr ⊂ » t) -/
theorem Finite.strong_induction_on {s : Set α} {P : Set α → Prop} (hs : s.Finite)
    (IH : ∀ (t) (_ : t ⊆ s), (∀ (t₀) (_ : t₀ ⊂ t), P t₀) → P t) : P s :=
  by
  by_contra' hs'
  obtain ⟨s₀, hs₀, hmin⟩ := finite.exists_minimal_subset hs hs'
  simp_rw [Classical.not_not] at hmin
  exact hmin.1 (IH _ hs₀ hmin.2)

end Set

