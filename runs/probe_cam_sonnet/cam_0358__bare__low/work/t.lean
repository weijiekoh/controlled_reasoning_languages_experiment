import Mathlib
open scoped RealInnerProductSpace
example {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ_symm : Q.IsSymm) (h1 : Q * Q⁻¹ = 1) : False := by
  have hsa : ∀ u v, ⟪u, Matrix.toEuclideanLin Q v⟫ = ⟪Matrix.toEuclideanLin Q u, v⟫ := by
    intro u v
    simp only [Matrix.toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, hQ_symm.eq, dotProduct_comm]
  sorry
