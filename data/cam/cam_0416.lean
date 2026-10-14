import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-416»

def IsProperCone {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  (∀ ⦃x : Fin n → ℝ⦄, x ∈ K → ∀ ⦃a : ℝ⦄, 0 ≤ a → a • x ∈ K) ∧
  Convex ℝ K ∧
  IsClosed K ∧
  (Set.Nonempty (interior K)) ∧
  K ∩ (-K) = ({0} : Set (Fin n → ℝ))

def IsGeneralizedLogarithmOfDegree
    {n : ℕ}
    (K : Set (Fin n → ℝ))
    (ψ : interior K → ℝ)
    (θ : ℝ) : Prop :=
  IsProperCone K ∧
  (∃ ψext : (Fin n → ℝ) → ℝ,
    ContDiffOn ℝ 2 ψext (interior K) ∧
    (∀ y : interior K, ψ y = ψext y) ∧
    (∀ y : interior K,
      IsUnit
        ((Matrix.of fun i j : Fin n =>
            (fderiv ℝ
                (fun x : Fin n → ℝ =>
                  (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
                (y : Fin n → ℝ))
              (Pi.single i (1 : ℝ))).det)) ∧
    (∀ (y : interior K) {t : ℝ}, 0 < t →
      ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
        ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t))

def GeneralizedLogarithmDegree
    {n : ℕ}
    (K : Set (Fin n → ℝ))
    (ψ : interior K → ℝ)
    (θ : ℝ) : Prop :=
  ∀ (y : interior K) {t : ℝ}, 0 < t →
    ∃ hy' : t • (y : Fin n → ℝ) ∈ interior K,
      ψ ⟨t • (y : Fin n → ℝ), hy'⟩ = ψ y + θ * Real.log t

theorem generalizedLogarithm_gradient_hessian_inverse_quadratic_form_eq_neg_degree
    {n : ℕ}
    {K : Set (Fin n → ℝ)}
    {ψ : interior K → ℝ}
    {θ : ℝ}
    (hψ : IsGeneralizedLogarithmOfDegree K ψ θ) :
    ∀ y : interior K,
      let ψext : (Fin n → ℝ) → ℝ := Classical.choose hψ.2
      let g : Fin n → ℝ := fun i =>
        (fderiv ℝ ψext (y : Fin n → ℝ)) (Pi.single i (1 : ℝ))
      let H : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n =>
        (fderiv ℝ
            (fun x : Fin n → ℝ =>
              (fderiv ℝ ψext x) (Pi.single j (1 : ℝ)))
            (y : Fin n → ℝ))
          (Pi.single i (1 : ℝ))
      dotProduct g (H⁻¹.mulVec g) = -θ := by
  sorry

end «CAM-Bench-416»
