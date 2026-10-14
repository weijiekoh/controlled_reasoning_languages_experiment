import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-88»

open scoped Matrix

def IsNewtonStep {n : ℕ} (r : (Fin n → ℝ) → (Fin n → ℝ)) (xk pk : Fin n → ℝ) : Prop :=
  fderiv ℝ r xk pk = -r xk

def NewtonNext {n : ℕ} (r : (Fin n → ℝ) → (Fin n → ℝ)) (xk xk1 pk : Fin n → ℝ) : Prop :=
  xk1 = xk + pk ∧ IsNewtonStep r xk pk

def IsNewtonMethodStep {n : ℕ} (r : (Fin n → ℝ) → (Fin n → ℝ)) (xk xk1 pk : Fin n → ℝ) : Prop :=
  NewtonNext r xk xk1 pk

theorem newton_step_invariant_under_equation_scaling
    {n : ℕ}
    (r : (Fin n → ℝ) → (Fin n → ℝ))
    (xk pk p_tilde_k c : Fin n → ℝ)
    (hr : DifferentiableAt ℝ r xk)
    (hwell :
      ∀ p₁ p₂ : Fin n → ℝ, IsNewtonStep r xk p₁ → IsNewtonStep r xk p₂ → p₁ = p₂)
    (hpk : IsNewtonStep r xk pk)
    (hc : ∀ i, c i ≠ 0)
    (hbridge :
      ∀ p : Fin n → ℝ,
        IsNewtonStep (fun x i => c i * r x i) xk p ↔ IsNewtonStep r xk p)
    (hscaled :
      IsNewtonStep (fun x i => c i * r x i) xk p_tilde_k) :
    p_tilde_k = pk := by
  sorry

end «CAM-Bench-88»
