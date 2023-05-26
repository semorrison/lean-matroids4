import Mathlib.SetTheory.Cardinal.Finite

variable {α : Type _} [Fintype α]

namespace Nat

theorem card_eq_toFinset_card (s : Set α) [DecidablePred (· ∈ s)] : Nat.card s = s.toFinset.card :=
  by simp [card_eq_fintype_card]

end Nat

