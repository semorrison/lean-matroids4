import Mathlib.Order.BooleanAlgebra

variable {α : Type _} [BooleanAlgebra α]

@[simp]
theorem sdiff_sdiff_cancel_right (a b : α) : a \ (b \ a) = a :=
  disjoint_sdiff_self_right.sdiff_eq_left

