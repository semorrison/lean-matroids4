import Mathlib.Tactic.Default

universe u

-- Is there a reason this obvious @[simp] lemma wasn't in mathlib ?
@[simp]
theorem Equiv.sumEquivSigmaBool_apply (α β : Type u) (x : Sum α β) :
    Equiv.sumEquivSigmaBool α β x = Sum.elim (Sigma.mk true) (Sigma.mk false) x :=
  rfl

