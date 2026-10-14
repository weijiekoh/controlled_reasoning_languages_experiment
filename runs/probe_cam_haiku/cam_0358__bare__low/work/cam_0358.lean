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
  set L := Matrix.toEuclideanLin Q with hL
  have hsymm : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪x, L y⟫ = ⟪y, L x⟫ := by
    intro x y
    simp only [hL, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply, dotProduct, Matrix.mulVec]
    simp only [star_trivial]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hQ_symm.apply i j
    rw [this]; ring
  have hdet : Q.det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have hw : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h; apply hv; simpa using congrArg WithLp.ofLp h
    have h0 : L (WithLp.toLp 2 v) = 0 := by
      simp only [hL, Matrix.toEuclideanLin_apply, hmv]; simp
    have := hQ_pos_def _ hw
    rw [h0, inner_zero_right] at this
    exact lt_irrefl _ this
  have hU : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  have hLM : ∀ x, L (Q⁻¹.toEuclideanLin x) = x := by
    intro x
    have : L (Matrix.toEuclideanLin Q⁻¹ x) = Matrix.toEuclideanLin (Q * Q⁻¹) x := by simp [hL]
    rw [this, Matrix.mul_nonsing_inv _ hU]; simp
  have hML : ∀ x, Matrix.toEuclideanLin Q⁻¹ (L x) = x := by
    intro x
    have : Matrix.toEuclideanLin Q⁻¹ (L x) = Matrix.toEuclideanLin (Q⁻¹ * Q) x := by simp [hL]
    rw [this, Matrix.nonsing_inv_mul _ hU]; simp
  set M := Matrix.toEuclideanLin Q⁻¹ with hM
  constructor
  · intro hsub
    intro i
    by_contra hA
    push_neg at hA
    have hApos : 0 < ⟪a i, L (a i)⟫ := by linarith [hA]
    have hsq : 0 < √(⟪a i, L (a i)⟫) := Real.sqrt_pos.mpr hApos
    have hsq2 : √(⟪a i, L (a i)⟫) * √(⟪a i, L (a i)⟫) = ⟪a i, L (a i)⟫ :=
      Real.mul_self_sqrt hApos.le
    have hc : ⟪L (a i), a i⟫ = ⟪a i, L (a i)⟫ := real_inner_comm (a i) (L (a i))
    have hmem : (1 / √(⟪a i, L (a i)⟫)) • L (a i) ∈
        {x : EuclideanSpace ℝ (Fin n) | ⟪x, M x⟫ ≤ (1:ℝ)} := by
      show ⟪(1 / √(⟪a i, L (a i)⟫)) • L (a i), M ((1 / √(⟪a i, L (a i)⟫)) • L (a i))⟫ ≤ 1
      rw [map_smul, hML, real_inner_smul_left, real_inner_smul_right, hc]
      have : 1 / √(⟪a i, L (a i)⟫) * (1 / √(⟪a i, L (a i)⟫) * ⟪a i, L (a i)⟫) = 1 := by
        field_simp
        linarith [hsq2]
      linarith
    have h2 := (hsub hmem) i
    rw [real_inner_smul_right] at h2
    have h3 : 1 / √(⟪a i, L (a i)⟫) * ⟪a i, L (a i)⟫ = √(⟪a i, L (a i)⟫) := by
      field_simp
      linarith [hsq2]
    rw [h3] at h2
    nlinarith [h2.2, hsq2]
  · intro h x hx i
    have hxL : L (M x) = x := hLM x
    set v := M x with hv
    have hC : ⟪v, L v⟫ ≤ 1 := by
      rw [real_inner_comm, hxL]; exact hx
    have hA := h i
    have hpsd : ∀ w : EuclideanSpace ℝ (Fin n), 0 ≤ ⟪w, L w⟫ := by
      intro w
      rcases eq_or_ne w 0 with h0 | h0
      · simp [h0]
      · exact (hQ_pos_def w h0).le
    have hw := hpsd (⟪a i, x⟫ • a i - v)
    have hsv : ⟪v, L (a i)⟫ = ⟪a i, L v⟫ := (hsymm _ _)
    have expand : ⟪⟪a i, x⟫ • a i - v, L (⟪a i, x⟫ • a i - v)⟫
        = ⟪a i, x⟫ * ⟪a i, x⟫ * ⟪a i, L (a i)⟫ - ⟪a i, x⟫ * ⟪a i, L v⟫
          - ⟪a i, x⟫ * ⟪v, L (a i)⟫ + ⟪v, L v⟫ := by
      rw [← hxL]
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right]
      ring
    have hcx : ⟪a i, L v⟫ = ⟪a i, x⟫ := by rw [hxL]
    rw [expand, hsv, hcx] at hw
    have hcc : ⟪a i, x⟫ * ⟪a i, x⟫ ≤ 1 := by
      nlinarith [mul_nonneg (mul_self_nonneg ⟪a i, x⟫) (sub_nonneg.2 hA)]
    constructor <;> nlinarith [hcc]

end «CAM-Bench-358»
