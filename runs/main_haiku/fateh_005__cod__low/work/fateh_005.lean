import Mathlib

/--
Let $R$ be a ring with $1 \neq 0$. For two elements $a,b \in R$, if $1-ab$ is a unit,
then $1-ba$ is a unit.
-/
theorem isUnit_one_sub_mul {R : Type} [Ring R] [Nontrivial R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  set w : R := ((u⁻¹ : Rˣ) : R) with hw
  have e1 : (1 - a * b) * w = 1 := by rw [← hu, hw]; exact u.mul_inv
  have e2 : w * (1 - a * b) = 1 := by rw [← hu, hw]; exact u.inv_mul
  have k1 : a * b * w = w - 1 := by
    rw [sub_mul, one_mul] at e1
    exact eq_sub_of_add_eq (by rw [← e1]; abel)
  have k2 : w * (a * b) = w - 1 := by
    rw [mul_sub, mul_one] at e2
    exact eq_sub_of_add_eq (by rw [← e2]; abel)
  have t1 : b * a * b * w * a = b * w * a - b * a := by
    rw [show b * a * b * w * a = b * (a * b * w) * a by noncomm_ring, k1]
    noncomm_ring
  have r : (1 - b * a) * (1 + b * w * a) = 1 := by
    have : (1 - b * a) * (1 + b * w * a) = 1 + b * w * a - b * a - b * a * b * w * a := by
      noncomm_ring
    rw [this, t1]; abel
  have l : (1 + b * w * a) * (1 - b * a) = 1 := by
    have : (1 + b * w * a) * (1 - b * a) = 1 + b * w * a - b * a - b * w * (a * b) * a := by
      noncomm_ring
    rw [this, show b * w * (a * b) * a = b * (w * (a * b)) * a by noncomm_ring, k2]
    noncomm_ring
  exact ⟨⟨1 - b * a, 1 + b * w * a, r, l⟩, rfl⟩
