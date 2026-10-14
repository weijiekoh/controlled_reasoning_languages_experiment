import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-10»

def NewtonDirection (r : (Fin n → ℝ) → Fin n → ℝ) (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (_hJ : Invertible (J x)) : Fin n → ℝ :=
  -((J x)⁻¹).mulVec (r x)

def ExactLineSearch (f : ℝ → ℝ) (x p : ℝ) : Set ℝ :=
  {α | ∀ β : ℝ, f (x + α * p) ≤ f (x + β * p)}

def euclideanNorm {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, x i ^ 2)

theorem exactLineSearch_step_tends_to_one_near_nonsingular_root
    {n : ℕ}
    (hn : 0 < n)
    (r : (Fin n → ℝ) → Fin n → ℝ)
    (J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hJ : ∀ x, J x = Matrix.of (fun i j =>
      (fderiv ℝ r x (Pi.single j (1 : ℝ))) i))
    (hrC1 : ContDiff ℝ 1 r)
    (xStar : Fin n → ℝ)
    (x : ℕ → Fin n → ℝ)
    (α : ℕ → ℝ)
    (p : ℕ → Fin n → ℝ)
    (hp : ∀ᶠ k in Filter.atTop,
      ∃ hJk : Invertible (J (x k)),
        p k = NewtonDirection r J (x k) hJk)
    (hk : ∀ᶠ k in Filter.atTop,
      ∃ hJk : Invertible (J (x k)),
        α k ∈ {a : ℝ |
          ∀ b : ℝ,
            (1 / 2 : ℝ) * euclideanNorm (r (x k + a • p k)) ^ 2 ≤
              (1 / 2 : ℝ) * euclideanNorm (r (x k + b • p k)) ^ 2})
    (hrstar : r xStar = 0)
    (hJstar : Invertible (J xStar))
    (hx : Filter.Tendsto x Filter.atTop (𝓝 xStar)) :
    Filter.Tendsto α Filter.atTop (𝓝 1) := by
  sorry

end «CAM-Bench-10»
