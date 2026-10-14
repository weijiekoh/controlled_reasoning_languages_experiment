import Mathlib

/--
Let $R$ be a ring with $1 \neq 0$. For two elements $a,b \in R$, if $1-ab$ is a unit,
then $1-ba$ is a unit.
-/
theorem isUnit_one_sub_mul {R : Type} [Ring R] [Nontrivial R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨u, hu⟩ := h
  have hv : (↑u⁻¹ : R) * (1 - a * b) = 1 := by
    rw [← hu]; exact u.inv_mul
  have hw : (1 - a * b) * (↑u⁻¹ : R) = 1 := by
    rw [← hu]; exact u.mul_inv
  refine ⟨⟨1 - b * a, 1 + b * (↑u⁻¹ : R) * a, ?_, ?_⟩, rfl⟩
  · have e : (1 - b * a) * (1 + b * (↑u⁻¹ : R) * a)
        = 1 + b * ((1 - a * b) * (↑u⁻¹ : R) - 1) * a := by noncomm_ring
    rw [e, hw]; simp
  · have e : (1 + b * (↑u⁻¹ : R) * a) * (1 - b * a)
        = 1 + b * ((↑u⁻¹ : R) * (1 - a * b) - 1) * a := by noncomm_ring
    rw [e, hv]; simp
