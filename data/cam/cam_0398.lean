import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-398»

def Hessian (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hf : ContDiffAt ℝ 2 f x) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x) (Pi.single i (1 : ℝ))

theorem saddle_residual_deriv_inverse_norm_le
    (p q : ℕ)
    (f : (Fin (p + q) → ℝ) → ℝ)
    (m : ℝ)
    (hdom :
      ∀ x : Fin (p + q) → ℝ, ContDiffAt ℝ 2 f x)
    (hm : 0 < m)
    (huu :
      ∀ x : Fin (p + q) → ℝ,
        ∀ u : Fin p → ℝ,
          m * ‖u‖^2 ≤
            ∑ i : Fin p, ∑ j : Fin p,
              u i * (Hessian (p + q) f x (hdom x) (Fin.castAdd q i) (Fin.castAdd q j)) * u j)
    (hvv :
      ∀ x : Fin (p + q) → ℝ,
        ∀ v : Fin q → ℝ,
          ∑ i : Fin q, ∑ j : Fin q,
            v i * (Hessian (p + q) f x (hdom x) (Fin.natAdd p i) (Fin.natAdd p j)) * v j
            ≤ -m * ‖v‖^2) :
    ∀ x : Fin (p + q) → ℝ,
    let H : Matrix (Fin (p + q)) (Fin (p + q)) ℝ := Hessian (p + q) f x (hdom x)
    let S : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
      fun i j =>
        if i = j then
          if (i : ℕ) < p then 1 else -1
        else 0
    let r : (Fin (p + q) → ℝ) → (Fin (p + q) → ℝ) :=
      fun y i =>
        if (i : ℕ) < p then
          (fderiv ℝ f y) (Pi.single i (1 : ℝ))
        else
          -((fderiv ℝ f y) (Pi.single i (1 : ℝ)))
    let Dr : Matrix (Fin (p + q)) (Fin (p + q)) ℝ :=
      fun i j => (fderiv ℝ r x (Pi.single j (1 : ℝ))) i
    Dr = S * H ∧ ‖Dr⁻¹‖ = ‖H⁻¹ * S‖ ∧ ‖H⁻¹ * S‖ = ‖H⁻¹‖ ∧ ‖H⁻¹‖ ≤ 1 / m := by
  sorry

end «CAM-Bench-398»
