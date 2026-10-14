import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-617»

def feasibleSet {α ι : Type*} (constraints : ι → α → Prop) : Set α :=
  {x | ∀ i, constraints i x}

structure CongruenceTransformedSemidefiniteProgram where
  n : ℕ
  m : ℕ
  c : Fin n → ℝ
  F : Fin n → Matrix (Fin m) (Fin m) ℝ
  G : Matrix (Fin m) (Fin m) ℝ

def CongruenceTransformedSemidefiniteProgram.constraintMatrix
    (p : CongruenceTransformedSemidefiniteProgram) (x : Fin p.n → ℝ) :
    Matrix (Fin p.m) (Fin p.m) ℝ :=
  ∑ i : Fin p.n, x i • p.F i + p.G

def CongruenceTransformedSemidefiniteProgram.isFeasible
    (p : CongruenceTransformedSemidefiniteProgram) : Set (Fin p.n → ℝ) :=
  feasibleSet (fun (_ : Unit) x => Matrix.PosSemidef (-p.constraintMatrix x))

def CongruenceTransformedSemidefiniteProgram.objective
    (p : CongruenceTransformedSemidefiniteProgram) (x : Fin p.n → ℝ) : ℝ :=
  ∑ i : Fin p.n, p.c i * x i

theorem congruenceTransform_preserves_feasibleSet_and_objective
    {n k : ℕ} (c : Fin n → ℝ) (F : Fin n → Matrix (Fin k) (Fin k) ℝ)
    (G R : Matrix (Fin k) (Fin k) ℝ) (hF : ∀ i, (F i).IsSymm) (hG : G.IsSymm)
    (hR : R.det ≠ 0) :
    let p : CongruenceTransformedSemidefiniteProgram :=
      { n := n
        m := k
        c := c
        F := fun i => R.transpose * F i * R
        G := R.transpose * G * R }
    let S : Set (Fin n → ℝ) :=
      feasibleSet (fun (_ : Unit) x => Matrix.PosSemidef (-(∑ i : Fin n, x i • F i + G)))
    let Sol : Set (Fin n → ℝ) :=
      {x | x ∈ S ∧ ∀ y ∈ S, (∑ i : Fin n, c i * x i) ≤ ∑ i : Fin n, c i * y i}
    let pSol : Set (Fin n → ℝ) :=
      {x | x ∈ p.isFeasible ∧ ∀ y ∈ p.isFeasible, p.objective x ≤ p.objective y}
    S = p.isFeasible ∧
      sInf ((fun x : Fin n → ℝ => ∑ i : Fin n, c i * x i) '' S) = sInf (p.objective '' p.isFeasible) ∧
      Sol = pSol := by
  sorry

end «CAM-Bench-617»
