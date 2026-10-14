import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-708»

open scoped Matrix
local notation "newtonDecrementHessian" =>
  fun {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) =>
    Matrix.of fun i j : Fin n =>
      (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

def newtonDecrement {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (_h_twice : ContDiffAt ℝ 2 f x)
    [Invertible (newtonDecrementHessian f x)] : ℝ :=
  let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
  let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
  Real.sqrt (dotProduct grad (⅟ hess *ᵥ grad))

theorem newtonDecrement_eq_sup_normalized_and_rayleigh_quotient
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (h_twice : ContDiffAt ℝ 2 f x)
    [Invertible (newtonDecrementHessian f x)]
    (hpd : Matrix.PosDef (newtonDecrementHessian f x)) :
    let grad : Fin n → ℝ := fun i => (fderiv ℝ f x) (Pi.single i (1 : ℝ))
    let hess : Matrix (Fin n) (Fin n) ℝ := newtonDecrementHessian f x
    newtonDecrement f x h_twice =
      sSup {r : ℝ | ∃ v : Fin n → ℝ, dotProduct v (hess *ᵥ v) = 1 ∧ r = -dotProduct v grad} ∧
    sSup {r : ℝ | ∃ v : Fin n → ℝ, dotProduct v (hess *ᵥ v) = 1 ∧ r = -dotProduct v grad} =
      sSup
        {r : ℝ |
          ∃ v : Fin n → ℝ,
            v ≠ 0 ∧
            r = (-dotProduct v grad) / Real.sqrt (dotProduct v (hess *ᵥ v))} := by
  sorry

end «CAM-Bench-708»
