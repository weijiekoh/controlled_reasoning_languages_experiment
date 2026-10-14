import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-262»

open scoped BigOperators

def convexConjugate {n : ℕ} (g : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {r | ∃ x : Fin n → ℝ, r = (∑ i, y i * x i) - g x}

def scalarConvexConjugate (h : ℝ → EReal) : ℝ → EReal :=
  fun s => sSup {r | ∃ t : ℝ, r = (s * t : ℝ) - h t}

theorem convexConjugate_radial_eq_scalarConvexConjugate_norm
    {n : ℕ} (h : ℝ → ℝ)
    (h_convex : ConvexOn ℝ Set.univ h)
    (h_monotone : Monotone h)
    (h_nonpos_const : ∀ t : ℝ, t ≤ 0 → h t = h 0) :
    convexConjugate (fun x : Fin n → ℝ => (h ‖x‖ : EReal)) =
      fun y : Fin n → ℝ => scalarConvexConjugate (fun t => (h t : EReal)) ‖y‖ := by
  sorry

end «CAM-Bench-262»
