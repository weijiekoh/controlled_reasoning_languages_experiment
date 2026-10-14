import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-536»

def perspectiveDomain {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) : Set ((Fin n → ℝ) × ℝ) :=
  {xt | 0 < xt.2 ∧ f (fun i => xt.1 i / xt.2) < ⊤}

def perspectiveFunction {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) :
    ((Fin n → ℝ) × ℝ) → WithTop ℝ :=
  fun xt =>
    if 0 < xt.2 then
      ((xt.2 : ℝ) : WithTop ℝ) * f (fun i => xt.1 i / xt.2)
    else
      ⊤

theorem perspectiveFunction_convexOn
    {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ)
    (hf_convex : Convex ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)}) :
    let D := perspectiveDomain f
    let g := perspectiveFunction f
    Convex ℝ D ∧
      ∀ x y : (Fin n → ℝ) × ℝ, x ∈ D → y ∈ D → ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        g ((fun i => θ * x.1 i + (1 - θ) * y.1 i), θ * x.2 + (1 - θ) * y.2) ≤
          ((θ : ℝ) : WithTop ℝ) * g x + ((1 - θ : ℝ) : WithTop ℝ) * g y := by
  sorry

end «CAM-Bench-536»
