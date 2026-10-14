import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-35»

def IsBasicFeasiblePoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧
    A.mulVec x = b ∧
    ∃ s : Finset (Fin n),
      ∃ hcard : s.card = m,
        IsUnit (Matrix.det (A.submatrix (fun i : Fin m => i) (fun i : Fin m => ↑(s.orderEmbOfFin hcard i)))) ∧
        (∀ i, i ∉ s → x i = 0) ∧
        let xs : Fin m → ℝ := fun i => x (s.orderEmbOfFin hcard i)
        let B : Matrix (Fin m) (Fin m) ℝ :=
          A.submatrix (fun i : Fin m => i) (fun i : Fin m => ↑(s.orderEmbOfFin hcard i))
        B.mulVec xs = b

def IsFeasibleVector {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  A.mulVec x = b ∧ ∀ i, 0 ≤ x i

structure LinearProgram where
  m : ℕ
  n : ℕ
  hmn : m ≤ n
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ

def LinearProgram.isFeasible (P : LinearProgram) (x : Fin P.n → ℝ) : Prop :=
  IsFeasibleVector P.A P.b x

def LinearProgram.objective (P : LinearProgram) (x : Fin P.n → ℝ) : ℝ :=
  P.c ⬝ᵥ x

theorem no_basic_feasible_points_of_rows_linearly_dependent
    (P : LinearProgram)
    (hdep : ¬ LinearIndependent ℝ (fun i : Fin P.m => P.A i)) :
    ¬ ∃ x : Fin P.n → ℝ, IsBasicFeasiblePoint P.A P.b x := by
  sorry

end «CAM-Bench-35»
