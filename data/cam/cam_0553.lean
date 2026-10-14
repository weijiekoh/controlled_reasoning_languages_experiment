import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-553»

open scoped ENNReal

theorem W_quasiconcave
    (n : ℕ)
    (f0 : ℝ → ℝ)
    (f : Fin n → ℝ → ℝ)
    (hf0 : Continuous f0)
    (hf : ∀ i, Continuous (f i))
    {ε : ℝ}
    (hε : 0 < ε) :
    let W : (Fin n → ℝ) → WithTop ℝ :=
      fun x =>
        sSup {T : WithTop ℝ |
          ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) ≤ T →
            |(∑ i : Fin n, x i * (f i t)) - f0 t| ≤ ε}
    ∀ x y : Fin n → ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      min (W x) (W y) ≤ W (fun i => θ * x i + (1 - θ) * y i) := by
  sorry

end «CAM-Bench-553»
