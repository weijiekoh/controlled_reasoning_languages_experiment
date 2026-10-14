import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-685»

structure MaximumMarginSeparationData (n N M : ℕ) where
  x : Fin N → EuclideanSpace ℝ (Fin n)
  y : Fin M → EuclideanSpace ℝ (Fin n)
  a : EuclideanSpace ℝ (Fin n)
  b : ℝ
  t : ℝ
  pos_t : 0 < t
  x_margin : ∀ i : Fin N, ⟪a, x i⟫ - b ≥ t
  y_margin : ∀ j : Fin M, ⟪a, y j⟫ - b ≤ -t
  norm_a_le_one : ‖a‖ ≤ 1

open scoped RealInnerProductSpace

structure MaximumMarginSeparationProblem (n N M : ℕ) where
  data : MaximumMarginSeparationData n N M

def MaximumMarginSeparationProblem.x {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : Fin N → EuclideanSpace ℝ (Fin n) :=
  p.data.x

def MaximumMarginSeparationProblem.y {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : Fin M → EuclideanSpace ℝ (Fin n) :=
  p.data.y

def MaximumMarginSeparationProblem.a {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : EuclideanSpace ℝ (Fin n) :=
  p.data.a

def MaximumMarginSeparationProblem.b {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : ℝ :=
  p.data.b

def MaximumMarginSeparationProblem.t {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : ℝ :=
  p.data.t

def MaximumMarginSeparationProblem.aTilde {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : EuclideanSpace ℝ (Fin n) :=
  p.t⁻¹ • p.a

def MaximumMarginSeparationProblem.bTilde {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : ℝ :=
  p.b / p.t

private lemma aTilde_sub_bTilde_eq_div
    {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M)
    (u : EuclideanSpace ℝ (Fin n)) :
    ⟪p.aTilde, u⟫ - p.bTilde = (⟪p.a, u⟫ - p.b) / p.t := by
  simp [MaximumMarginSeparationProblem.aTilde, MaximumMarginSeparationProblem.bTilde,
    div_eq_mul_inv, inner_smul_left, sub_eq_add_neg, mul_add, mul_comm]

private lemma x_separation_from_margin
    {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M)
    (i : Fin N) :
    ⟪p.aTilde, p.x i⟫ - p.bTilde ≥ 1 := by
  have ht : 0 < p.t := p.data.pos_t
  have ht_ne : p.t ≠ 0 := ne_of_gt ht
  have hscaled : 1 ≤ (⟪p.a, p.x i⟫ - p.b) / p.t := by
    have hdiv :
        p.t / p.t ≤ (⟪p.a, p.x i⟫ - p.b) / p.t :=
      div_le_div_of_nonneg_right (p.data.x_margin i) (le_of_lt ht)
    simpa [div_self ht_ne] using hdiv
  calc
    ⟪p.aTilde, p.x i⟫ - p.bTilde = (⟪p.a, p.x i⟫ - p.b) / p.t :=
      aTilde_sub_bTilde_eq_div p (p.x i)
    _ ≥ 1 := hscaled

private lemma y_separation_from_margin
    {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M)
    (j : Fin M) :
    ⟪p.aTilde, p.y j⟫ - p.bTilde ≤ -1 := by
  have ht : 0 < p.t := p.data.pos_t
  have ht_ne : p.t ≠ 0 := ne_of_gt ht
  have hscaled : (⟪p.a, p.y j⟫ - p.b) / p.t ≤ -1 := by
    have hdiv :
        (⟪p.a, p.y j⟫ - p.b) / p.t ≤ (-p.t) / p.t :=
      div_le_div_of_nonneg_right (p.data.y_margin j) (le_of_lt ht)
    have hneg : (-p.t) / p.t = (-1 : ℝ) := by
      field_simp [ht_ne]
    simpa [hneg] using hdiv
  calc
    ⟪p.aTilde, p.y j⟫ - p.bTilde = (⟪p.a, p.y j⟫ - p.b) / p.t :=
      aTilde_sub_bTilde_eq_div p (p.y j)
    _ ≤ -1 := hscaled

structure MinimumNormSeparatingHyperplaneProblem (n N M : ℕ) where
  x : Fin N → EuclideanSpace ℝ (Fin n)
  y : Fin M → EuclideanSpace ℝ (Fin n)
  aTilde : EuclideanSpace ℝ (Fin n)
  bTilde : ℝ
  x_separation : ∀ i : Fin N, ⟪aTilde, x i⟫ - bTilde ≥ 1
  y_separation : ∀ j : Fin M, ⟪aTilde, y j⟫ - bTilde ≤ -1

def MinimumNormSeparatingHyperplaneProblem.objective {n N M : ℕ}
    (p : MinimumNormSeparatingHyperplaneProblem n N M) : ℝ :=
  ‖p.aTilde‖

def MaximumMarginSeparationProblem.toMinimumNormSeparatingHyperplaneProblem {n N M : ℕ}
    (p : MaximumMarginSeparationProblem n N M) : MinimumNormSeparatingHyperplaneProblem n N M where
  x := p.x
  y := p.y
  aTilde := p.aTilde
  bTilde := p.bTilde
  x_separation := by
    exact x_separation_from_margin p
  y_separation := by
    exact y_separation_from_margin p

theorem maximum_margin_separation_equivalent_to_minimum_norm_hyperplane
    {n N M : ℕ} (p : MaximumMarginSeparationProblem n N M) :
    let q := p.toMinimumNormSeparatingHyperplaneProblem
    MinimumNormSeparatingHyperplaneProblem.objective q = ‖p.a‖ / p.t ∧
    (‖p.a‖ = 1 → p.t = 1 / MinimumNormSeparatingHyperplaneProblem.objective q) := by
  sorry

end «CAM-Bench-685»
