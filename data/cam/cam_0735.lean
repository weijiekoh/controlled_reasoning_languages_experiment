import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-735»

def euclideanLength {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

structure QuadraticUnitBallProblem (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ
  A_symm : Matrix.IsSymm A

def QuadraticUnitBallProblem.objective {n : ℕ} (p : QuadraticUnitBallProblem n) (x : Fin n → ℝ) : ℝ :=
  dotProduct x (fun i => ∑ j, p.A i j * x j) + 2 * dotProduct p.b x

def QuadraticUnitBallProblem.isFeasible {n : ℕ} (_p : QuadraticUnitBallProblem n) (x : Fin n → ℝ) : Prop :=
  euclideanLength x ≤ (1 : ℝ)

structure ShorLiftingSDP (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  b : Fin n → ℝ

def ShorLiftingSDP.objective {n : ℕ}
    (sdp : ShorLiftingSDP n) (p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) : ℝ :=
  Matrix.trace (sdp.A * p.1) + 2 * dotProduct sdp.b p.2

def ShorLiftingSDP.feasibleSet {n : ℕ}
    (_sdp : ShorLiftingSDP n) : Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {p |
    let X := p.1
    let x := p.2
    Matrix.IsSymm X ∧
    Matrix.trace X ≤ 1 ∧
    Matrix.PosSemidef
      (Matrix.fromBlocks X (fun i _ => x i) (fun _ j => x j)
        (![![1]] : Matrix (Fin 1) (Fin 1) ℝ))}

def ShorLiftingSDP.isFeasible {n : ℕ}
    (sdp : ShorLiftingSDP n) (z : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) : Prop :=
  z ∈ sdp.feasibleSet

theorem quadraticUnitBallProblem_dual_of_dual_eq_shor_lifting
    {n : ℕ} (p : QuadraticUnitBallProblem n) :
    let sdp : ShorLiftingSDP n := { A := p.A, b := p.b }
    ∀ x : Fin n → ℝ,
      p.isFeasible x →
        let X : Matrix (Fin n) (Fin n) ℝ := fun i j => x i * x j
        sdp.isFeasible (X, x) ∧
          sdp.objective (X, x) = p.objective x := by
  sorry

end «CAM-Bench-735»
