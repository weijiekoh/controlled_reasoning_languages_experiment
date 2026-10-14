import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-610»

def positiveOrthant (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 < x i}

def monomial (n : ℕ) (c : ℝ) (a : Fin n → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x => if hx : ∀ i, 0 < x i then c * ∏ i, x i ^ (a i) else 0

theorem monomial_matches_value_and_partials_at_point
    (n : ℕ)
    (f : (Fin n → ℝ) → ℝ)
    (x0 : Fin n → ℝ)
    (hf_pos : 0 < f x0)
    (hx0_pos : x0 ∈ positiveOrthant n)
    (f' : (Fin n → ℝ) →L[ℝ] ℝ)
    (hf_deriv : HasFDerivAt f f' x0) :
    let a : Fin n → ℝ := fun idx => (x0 idx / f x0) * f' (Pi.single idx 1)
    let c : ℝ := (f x0) / ∏ idx, x0 idx ^ (a idx)
    let fhat : (Fin n → ℝ) → ℝ := monomial n c a
    fhat x0 = f x0 ∧
      ∀ idx : Fin n,
        deriv (fun t : ℝ => fhat (Function.update x0 idx t)) (x0 idx) =
          deriv (fun t : ℝ => f (Function.update x0 idx t)) (x0 idx) := by
  sorry

end «CAM-Bench-610»
