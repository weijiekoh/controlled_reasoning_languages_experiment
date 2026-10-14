import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-291»

structure CardinalityConstrainedConvexProgram where
  n : ℕ
  m : ℕ
  k : ℕ
  hm_ge_k : k ≤ m
  f0 : (Fin n → ℝ) → ℝ
  fi : Fin m → (Fin n → ℝ) → ℝ
  f0_convex : ConvexOn ℝ Set.univ f0
  fi_convex : ∀ i : Fin m, ConvexOn ℝ Set.univ (fi i)

def CardinalityConstrainedConvexProgram.isFeasible
    (P : CardinalityConstrainedConvexProgram) (x : Fin P.n → ℝ) : Prop :=
  {i : Fin P.m | P.fi i x ≤ 0}.encard ≥ P.k

def CardinalityConstrainedConvexProgram.objective
    (P : CardinalityConstrainedConvexProgram) (x : Fin P.n → ℝ) : ℝ :=
  P.f0 x

theorem sum_posPart_le_cardinality_implies_feasible
    (P : CardinalityConstrainedConvexProgram) (x : Fin P.n → ℝ) (lam : ℝ)
    (h :
      ∑ i : Fin P.m, max (1 + lam * P.fi i x) 0 ≤ P.m - P.k)
    (hlam : 1 ≤ lam) :
    P.isFeasible x := by
  sorry

end «CAM-Bench-291»
