import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-549»

def IsClosedConvexFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsClosed {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
  Convex ℝ {p : (Fin n → ℝ) × ℝ | f p.1 ≤ (p.2 : EReal)}

def convexConjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun y => sSup {z : EReal | ∃ x : Fin n → ℝ, z = (∑ i, y i * x i : ℝ) - f x}

def biconjugate {n : ℕ} (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  convexConjugate (convexConjugate f)

theorem closed_convex_function_eq_biconjugate {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hclosedConv : IsClosedConvexFunction f) :
    f = biconjugate f := by
  sorry

end «CAM-Bench-549»
