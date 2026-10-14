import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-358»

theorem ellipsoid_subset_strip_polyhedron_iff
    {n p : ℕ}
    (a : Fin p → EuclideanSpace ℝ (Fin n))
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ_symm : Q.IsSymm)
    (hQ_pos_def : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < ⟪x, (Matrix.toEuclideanLin Q) x⟫)
    :
    ({x : EuclideanSpace ℝ (Fin n) |
        ⟪x, (Matrix.toEuclideanLin Q⁻¹) x⟫ ≤ (1 : ℝ)} ⊆
      {x : EuclideanSpace ℝ (Fin n) | ∀ i : Fin p, -1 ≤ ⟪a i, x⟫ ∧ ⟪a i, x⟫ ≤ 1}) ↔
    (∀ i : Fin p, ⟪a i, (Matrix.toEuclideanLin Q) (a i)⟫ ≤ (1 : ℝ)) := by
  have hdet : IsUnit Q.det := by
    rw [isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv, h⟩
    have := hQ_pos_def (WithLp.toLp 2 v) (by simpa using hv)
    simp [Matrix.toEuclideanLin_apply, h] at this
  have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hdet
  have hL : ∀ x, Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ x) = x := by
    intro x
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, h1]
  have hL' : ∀ x, Matrix.toEuclideanLin Q⁻¹ (Matrix.toEuclideanLin Q x) = x := by
    intro x
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, h2]
  have hsa : ∀ u v, ⟪u, Matrix.toEuclideanLin Q v⟫ = ⟪Matrix.toEuclideanLin Q u, v⟫ := by
    intro u v
    simp only [Matrix.toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
    simp [Matrix.dotProduct_mulVec, dotProduct_comm]
    rw [← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, hQ_symm.eq, Matrix.dotProduct_mulVec v, ← Matrix.mulVec_transpose, hQ_symm.eq, dotProduct_comm]
  have hnn : ∀ y : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪y, (Matrix.toEuclideanLin Q) y⟫ := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · exact (hQ_pos_def y hy).le
  constructor
  · intro h i
    set a0 := a i with ha
    set L := Matrix.toEuclideanLin Q with hLd
    by_cases h0 : a0 = 0
    · simp [h0]
    have hs : 0 < ⟪a0, L a0⟫ := hQ_pos_def a0 h0
    set s := ⟪a0, L a0⟫ with hsd
    have hr := Real.sqrt_pos.mpr hs
    have hr2 := Real.sq_sqrt hs.le
    set r := Real.sqrt s
    have hx : (r⁻¹ • L a0) ∈ {x : EuclideanSpace ℝ (Fin n) |
        ⟪x, (Matrix.toEuclideanLin Q⁻¹) x⟫ ≤ (1 : ℝ)} := by
      show ⟪r⁻¹ • L a0, (Matrix.toEuclideanLin Q⁻¹) (r⁻¹ • L a0)⟫ ≤ 1
      have hc : ⟪L a0, a0⟫ = s := real_inner_comm _ _
      rw [map_smul, hL', inner_smul_left, inner_smul_right, hc]
      simp only [conj_trivial]

      field_simp
      nlinarith
    have := (h hx i).2
    have e : ⟪a i, L a0⟫ = s := rfl
    rw [inner_smul_right, e] at this

    have : r⁻¹ * s = r := by field_simp; nlinarith
    nlinarith
  · intro h x hx i
    have hx' : ⟪x, (Matrix.toEuclideanLin Q⁻¹) x⟫ ≤ 1 := hx
    have e1 := hnn (Matrix.toEuclideanLin Q⁻¹ x - a i)
    have e2 := hnn (Matrix.toEuclideanLin Q⁻¹ x + a i)
    have hh := h i
    have c1 : ⟪Matrix.toEuclideanLin Q⁻¹ x, x⟫ = ⟪x, Matrix.toEuclideanLin Q⁻¹ x⟫ := real_inner_comm _ _
    have c2 : ⟪Matrix.toEuclideanLin Q⁻¹ x, Matrix.toEuclideanLin Q (a i)⟫ = ⟪a i, x⟫ := by
      rw [hsa, hL, real_inner_comm]
    have c4 : ⟪a i, Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ x)⟫ = ⟪a i, x⟫ := by rw [hL]
    simp only [map_sub, map_add, hL, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right] at e1 e2
    rw [c1, c2] at e1 e2
    constructor <;> nlinarith

end «CAM-Bench-358»
