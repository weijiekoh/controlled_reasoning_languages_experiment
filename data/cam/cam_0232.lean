import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-232»

open scoped BigOperators

def infimalConvolution (m n : ℕ) (f : Fin m → (EuclideanSpace ℝ (Fin n) → EReal))
    (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  sInf {r | ∃ y : Fin m → EuclideanSpace ℝ (Fin n), (∑ i, y i) = x ∧ r = ∑ i, f i (y i)}

theorem infimalConvolution_convex
    (m n : ℕ)
    (f : Fin m → (EuclideanSpace ℝ (Fin n) → EReal))
    (hf : ∀ i : Fin m, ConvexOn ℝ Set.univ (fun x => EReal.toReal (f i x)))
    : ConvexOn ℝ Set.univ (fun x => EReal.toReal (infimalConvolution m n f x)) := by
  sorry

end «CAM-Bench-232»
