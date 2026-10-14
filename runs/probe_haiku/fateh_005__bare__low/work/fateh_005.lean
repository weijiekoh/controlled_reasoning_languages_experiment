import Mathlib

/--
Let $R$ be a ring with $1 \neq 0$. For two elements $a,b \in R$, if $1-ab$ is a unit,
then $1-ba$ is a unit.
-/
theorem isUnit_one_sub_mul {R : Type} [Ring R] [Nontrivial R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  set w : R := ↑u⁻¹ with hwdef
  have hw1 : (1 - a * b) * w = 1 := by
    rw [hwdef, ← hu]; exact u.mul_inv
  have hw2 : w * (1 - a * b) = 1 := by
    rw [hwdef, ← hu]; exact u.inv_mul
  have h3 : a * b * w = w - 1 := by
    rw [sub_mul, one_mul] at hw1
    rw [← sub_eq_zero, ← hw1]; abel
  have h4 : w * a * b = w - 1 := by
    rw [mul_sub, mul_one] at hw2
    rw [mul_assoc, ← sub_eq_zero, ← hw2]; abel
  have e1 : (1 - b * a) * (1 + b * w * a) = 1 := by
    have : b * (a * b * w) * a = b * w * a - b * a := by
      rw [h3]; noncomm_ring
    calc (1 - b * a) * (1 + b * w * a) = 1 + b * w * a - b * a - b * (a * b * w) * a := by noncomm_ring
      _ = 1 := by rw [this]; noncomm_ring
  have e2 : (1 + b * w * a) * (1 - b * a) = 1 := by
    have : b * (w * a * b) * a = b * w * a - b * a := by
      rw [h4]; noncomm_ring
    calc (1 + b * w * a) * (1 - b * a) = 1 + b * w * a - b * a - b * (w * a * b) * a := by noncomm_ring
      _ = 1 := by rw [this]; noncomm_ring
  exact ⟨⟨1 - b * a, 1 + b * w * a, e1, e2⟩, rfl⟩
