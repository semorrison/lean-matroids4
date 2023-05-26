import Mathlib.Data.Finset.Card

namespace Finset

variable {α : Type _} {s t : Finset α}

theorem exists_mem_sdiff_of_card_lt_card (h : s.card < t.card) : ∃ e, e ∈ t ∧ e ∉ s :=
  by
  refine' by_contra fun h' => h.not_le (card_mono fun x hx => _)
  push_neg  at h'
  exact h' _ hx

variable [DecidableEq α]

@[simp]
theorem card_inter_add_card_sdiff_eq_card (s t : Finset α) : (s ∩ t).card + (s \ t).card = s.card :=
  by convert@card_sdiff_add_card_eq_card _ _ _ _ _ <;> simp

theorem card_sdiff_eq_card_sdiff_iff_card_eq_card : s.card = t.card ↔ (s \ t).card = (t \ s).card :=
  by
  rw [← card_inter_add_card_sdiff_eq_card s t, ← card_inter_add_card_sdiff_eq_card t s, inter_comm,
    add_right_inj]

theorem card_le_card_iff_card_sdiff_le_card_sdiff : s.card ≤ t.card ↔ (s \ t).card ≤ (t \ s).card :=
  by
  rw [← card_inter_add_card_sdiff_eq_card s t, ← card_inter_add_card_sdiff_eq_card t s, inter_comm,
    add_le_add_iff_left]

theorem card_lt_card_iff_card_sdiff_lt_card_sdiff : s.card < t.card ↔ (s \ t).card < (t \ s).card :=
  by
  rw [← card_inter_add_card_sdiff_eq_card s t, ← card_inter_add_card_sdiff_eq_card t s, inter_comm,
    add_lt_add_iff_left]

end Finset

