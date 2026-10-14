import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-369»

def IsQuasiconvexOptimizationProblem
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (C : Set E) (f : E → ℝ) : Prop :=
  Convex ℝ C ∧ QuasiconvexOn ℝ C f

structure QuasiconvexMinimaxProblem where
  N : ℕ
  D : Set ℝ
  f : Fin N → ℝ → EuclideanSpace ℝ (Fin 2)
  y : Fin N → EuclideanSpace ℝ (Fin 2)

def QuasiconvexMinimaxProblem.objective (P : QuasiconvexMinimaxProblem) (x : ℝ) : ℝ :=
  sSup ((fun k : Fin P.N => ‖P.f k x - P.y k‖) '' Set.univ)

def QuasiconvexMinimaxProblem.is_feasible (P : QuasiconvexMinimaxProblem) (x : ℝ) : Prop :=
  x ∈ P.D

def QuasiconvexMinimaxProblem.is_quasiconvex_optimization_problem
    (P : QuasiconvexMinimaxProblem) : Prop :=
  IsQuasiconvexOptimizationProblem P.D P.objective

open scoped RealInnerProductSpace

theorem linearFractional_minimax_is_quasiconvex_optimization_problem
    (N : ℕ)
    (A : Fin N → Matrix (Fin 2) (Fin 3) ℝ)
    (b : Fin N → EuclideanSpace ℝ (Fin 2))
    (c : Fin N → EuclideanSpace ℝ (Fin 3))
    (d : Fin N → ℝ)
    (y : Fin N → EuclideanSpace ℝ (Fin 2))
    (hN : 1 ≤ N)

    (hRank :
      ∀ k : Fin N,
        Matrix.rank
          (Matrix.of (fun (i : Fin 3) (j : Fin 3) =>
            if hi : i.1 < 2 then A k ⟨i.1, hi⟩ j
            else c k j)) = 3)
    (hDne :
      ({x : EuclideanSpace ℝ (Fin 3) | ∀ k : Fin N, ⟪c k, x⟫ + d k > 0}).Nonempty) :
    let D : Set (EuclideanSpace ℝ (Fin 3)) :=
      {x | ∀ k : Fin N, ⟪c k, x⟫ + d k > 0}
    let f : Fin N → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2) :=
      fun k x =>
        (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).symm
          (((1 : ℝ) / (⟪c k, x⟫ + d k)) •
            ((A k).mulVec ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)) x) +
              (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)) (b k)))
    let g : EuclideanSpace ℝ (Fin 3) → ℝ :=
      fun x => sSup ((fun k : Fin N => ‖f k x - y k‖) '' Set.univ)
    IsQuasiconvexOptimizationProblem D g := by
  sorry

end «CAM-Bench-369»
