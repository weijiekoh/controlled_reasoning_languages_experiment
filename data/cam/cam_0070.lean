import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-70»

structure EqualityConstrainedQuadraticProgram (n ι : Type) [Fintype n] [DecidableEq n] where
  G : Matrix n n ℝ
  g : n → ℝ
  activeSet : Set ι
  a : ι → n → ℝ

def EqualityConstrainedQuadraticProgram.isFeasible
    {n ι : Type} [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram n ι) (p : n → ℝ) : Prop :=
  ∀ i, i ∈ P.activeSet → dotProduct (P.a i) p = 0

def EqualityConstrainedQuadraticProgram.objective
    {n ι : Type} [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram n ι) (p : n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * dotProduct p (fun i => ∑ j, P.G i j * p j) + dotProduct P.g p

theorem equalityConstrainedQuadraticProgram_line_restriction_minimal
    {n ι : Type} [Fintype n] [DecidableEq n]
    (P : EqualityConstrainedQuadraticProgram n ι)
    (xStar d : n → ℝ)
    (hxStar : P.isFeasible xStar)
    (hd : ∀ i, i ∈ P.activeSet → dotProduct (P.a i) d = 0) :
    let a : ℝ := (1 / 2 : ℝ) * dotProduct d (fun i => ∑ j, P.G i j * d j)
    let b : ℝ :=
      (1 / 2 : ℝ) *
        (dotProduct xStar (fun i => ∑ j, P.G i j * d j) +
          dotProduct d (fun i => ∑ j, P.G i j * xStar j)) +
        dotProduct P.g d
    let c : ℝ := P.objective xStar
    (∀ t : ℝ, P.isFeasible (xStar + t • d)) ∧
      ∀ t : ℝ,
        P.objective (xStar + t • d) = a * t ^ 2 + b * t + c := by
  sorry

end «CAM-Bench-70»
