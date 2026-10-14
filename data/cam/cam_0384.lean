import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-384»

def IsReducedIncidenceMatrix {m b : ℕ} (B : Matrix (Fin m) (Fin b) ℝ)
    (R : Matrix (Fin (m - 1)) (Fin b) ℝ) : Prop :=
  ∃ i : Fin m, ∃ e : Fin (m - 1) ≃ {j : Fin m // j ≠ i},
    R = fun r c => B (e r).1 c

structure CircuitCurrentConvexProgram (b m : ℕ) where
  A : Matrix (Fin m) (Fin b) ℝ
  ψ : (Fin b → ℝ) → ℝ

def CircuitCurrentConvexProgram.IsFeasible {b m : ℕ} (P : CircuitCurrentConvexProgram b m)
    (i : Fin b → ℝ) : Prop :=
  P.A.mulVec i = 0

def CircuitCurrentConvexProgram.ObjectiveValue {b m : ℕ} (P : CircuitCurrentConvexProgram b m)
    (i : Fin b → ℝ) : ℝ :=
  P.ψ i

def CircuitCurrentConvexProgram.IsOptimal {b m : ℕ} (P : CircuitCurrentConvexProgram b m)
    (i : Fin b → ℝ) : Prop :=
  P.IsFeasible i ∧ ∀ j : Fin b → ℝ, P.IsFeasible j → P.ObjectiveValue i ≤ P.ObjectiveValue j

theorem circuit_current_objective_convex
    {b a : ℕ} (P : CircuitCurrentConvexProgram b a)
    (phi : Fin b → ℝ → ℝ)
    (hpsi :
      ∀ i : Fin b → ℝ,
        P.ψ i = ∑ j : Fin b, ∫ u in (0)..(i j), phi j u)
    (hphi_mono : ∀ j : Fin b, Monotone (phi j))
    (hphi_cont : ∀ j : Fin b, Continuous (phi j)) :
    ConvexOn ℝ Set.univ P.ψ := by
  sorry

end «CAM-Bench-384»
