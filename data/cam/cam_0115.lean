import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-115»

open scoped RealInnerProductSpace

def steepestDescentNext {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (α : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  x + α • (-∇ f x)

def exactLineSearchObjective {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (α : ℝ) : Prop :=
  ∀ β : ℝ, f (x + α • p) ≤ f (x + β • p)

theorem steepestDescent_exactLineSearch_one_step_of_initialError_parallel_eigenvector
    {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (x0 xStar v : EuclideanSpace ℝ (Fin n)) (lam c α : ℝ)
    (hQ_symm : Q.IsSymm)
    (hQ_pos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x))
    (hxStar : Q.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) xStar) = b)
    (hv : v ≠ 0)
    (heig : Q.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) v) =
      lam • ((EuclideanSpace.equiv (Fin n) ℝ) v))
    (hx0 : x0 - xStar = c • v)
    (hα : 0 < α)
    (hαmin :
      exactLineSearchObjective
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 / 2 : ℝ) * dotProduct ((EuclideanSpace.equiv (Fin n) ℝ) x)
            (Q.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x)) -
            dotProduct b ((EuclideanSpace.equiv (Fin n) ℝ) x))
        x0 (-∇ (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 / 2 : ℝ) * dotProduct ((EuclideanSpace.equiv (Fin n) ℝ) x)
            (Q.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x)) -
            dotProduct b ((EuclideanSpace.equiv (Fin n) ℝ) x)) x0) α) :
    steepestDescentNext
        (fun x : EuclideanSpace ℝ (Fin n) =>
          (1 / 2 : ℝ) * dotProduct ((EuclideanSpace.equiv (Fin n) ℝ) x)
            (Q.mulVec ((EuclideanSpace.equiv (Fin n) ℝ) x)) -
            dotProduct b ((EuclideanSpace.equiv (Fin n) ℝ) x))
        x0 α = xStar := by
  sorry

end «CAM-Bench-115»
