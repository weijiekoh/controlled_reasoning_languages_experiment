import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-53»

open Matrix

theorem reducedHessianProjector_independent_of_basis
    {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]
    (H : Matrix n n ℝ) (N : Submodule ℝ (n → ℝ))
    (Q Z₁ Z₂ : Matrix n k ℝ) (B₁ B₂ : Matrix k k ℝ)
    (hQ : Qᵀ * Q = 1)
    (hZ₁ : Z₁ = Q * B₁)
    (hZ₂ : Z₂ = Q * B₂)
    (hspan₁ :
      Submodule.span ℝ
        (Set.range fun j : k => Z₁.mulVec (fun j' => if j' = j then 1 else 0)) = N)
    (hspan₂ :
      Submodule.span ℝ
        (Set.range fun j : k => Z₂.mulVec (fun j' => if j' = j then 1 else 0)) = N)
    (hB₁ : IsUnit B₁.det)
    (hB₂ : IsUnit B₂.det)
    (hZ₁HZ₁_inv : IsUnit ((Z₁ᵀ * H * Z₁).det))
    (hZ₂HZ₂_inv : IsUnit ((Z₂ᵀ * H * Z₂).det)) :
    Z₁ * (Z₁ᵀ * H * Z₁)⁻¹ * Z₁ᵀ = Z₂ * (Z₂ᵀ * H * Z₂)⁻¹ * Z₂ᵀ := by
  sorry

end «CAM-Bench-53»
