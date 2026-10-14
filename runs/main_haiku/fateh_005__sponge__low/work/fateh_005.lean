import Mathlib

/--
Let $R$ be a ring with $1 \neq 0$. For two elements $a,b \in R$, if $1-ab$ is a unit,
then $1-ba$ is a unit.
-/
theorem isUnit_one_sub_mul {R : Type} [Ring R] [Nontrivial R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  obtain ⟨v, hv⟩ := h
  have h1 : (v : R) * ((v⁻¹ : Rˣ) : R) = 1 := by simp
  have h2 : ((v⁻¹ : Rˣ) : R) * (v : R) = 1 := by simp
  rw [hv] at h1 h2
  generalize ((v⁻¹ : Rˣ) : R) = u at h1 h2 ⊢
  have hu1 : u - a * b * u = 1 := by simpa [sub_mul] using h1
  have hu2 : u - u * a * b = 1 := by simpa [mul_assoc, mul_sub] using h2
  have hk1 : a * b * u = u - 1 := by
    calc a * b * u = u - (u - a * b * u) := by abel
      _ = u - 1 := by rw [hu1]
  have hk2 : u * a * b = u - 1 := by
    calc u * a * b = u - (u - u * a * b) := by abel
      _ = u - 1 := by rw [hu2]
  refine ⟨⟨1 - b * a, 1 + b * u * a, ?_, ?_⟩, rfl⟩
  · calc (1 - b * a) * (1 + b * u * a) = 1 + b * u * a - b * a - b * (a * b * u) * a := by noncomm_ring
      _ = 1 := by rw [hk1]; noncomm_ring
  · calc (1 + b * u * a) * (1 - b * a) = 1 + b * u * a - b * a - b * (u * a * b) * a := by noncomm_ring
      _ = 1 := by rw [hk2]; noncomm_ring
