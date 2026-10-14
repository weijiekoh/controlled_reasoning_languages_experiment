import Mathlib

/--
Let $R$ be a ring with $1 \neq 0$. For two elements $a,b \in R$, if $1-ab$ is a unit,
then $1-ba$ is a unit.
-/
theorem isUnit_one_sub_mul {R : Type} [Ring R] [Nontrivial R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  have h1 : (1 - a * b) * ↑u⁻¹ = 1 := by rw [← hu]; exact u.mul_inv
  have h2 : (↑u⁻¹ : R) * (1 - a * b) = 1 := by rw [← hu]; exact u.inv_mul
  refine ⟨⟨1 - b * a, 1 + b * ↑u⁻¹ * a, ?_, ?_⟩, rfl⟩
  · calc (1 - b * a) * (1 + b * ↑u⁻¹ * a) = 1 - b * a + b * ((1 - a * b) * ↑u⁻¹) * a := by noncomm_ring
      _ = 1 := by rw [h1]; noncomm_ring
  · calc (1 + b * ↑u⁻¹ * a) * (1 - b * a) = 1 - b * a + b * (↑u⁻¹ * (1 - a * b)) * a := by noncomm_ring
      _ = 1 := by rw [h2]; noncomm_ring
