import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-648»

def Quasiconvex {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x z : Fin n → ℝ, ∀ θ : ℝ,
    0 ≤ θ → θ ≤ 1 →
      f (fun i => θ * x i + (1 - θ) * z i) ≤ max (f x) (f z)

theorem exists_quasiconvex_interpolant_iff_exists_separating_vectors
    (n m : ℕ) (u : Fin m → (Fin n → ℝ)) (y : Fin m → ℝ) :
    (∃ f : (Fin n → ℝ) → ℝ, Quasiconvex f ∧ ∀ i : Fin m, f (u i) = y i) ↔
    ∃ g : Fin m → (Fin n → ℝ),
      ∀ i j : Fin m, y j < y i → ∑ k : Fin n, g i k * ((u j) k - (u i) k) ≤ -1 := by
  sorry

end «CAM-Bench-648»
