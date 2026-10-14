import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-201»

structure SubsetDispersionMinimization where
  ι : Type
  col : Type
  E : Finset (Finset ι)
  X : ι → col
  fixed : Set ι
  f : Finset ι → (ι → col) → ℝ

def SubsetDispersionMinimization.feasible
    (p : SubsetDispersionMinimization) (Y : p.ι → p.col) : Prop :=
  ∀ j, j ∈ p.fixed → Y j = p.X j

def SubsetDispersionMinimization.objective
    (p : SubsetDispersionMinimization) (Y : p.ι → p.col) : ℝ :=
  Finset.sum p.E (fun S => p.f S Y)

def SubsetDispersionMinimization.isFree (p : SubsetDispersionMinimization) (j : p.ι) : Prop :=
  j ∉ p.fixed

def SubsetDispersionMinimization.IsSolution
    (p : SubsetDispersionMinimization) (Y : p.ι → p.col) : Prop :=
  p.feasible Y ∧ ∀ Z : p.ι → p.col, p.feasible Z → p.objective Y ≤ p.objective Z

theorem subsetDispersionMinimization_convex_in_free_coordinates
    (p : SubsetDispersionMinimization)
    [AddCommMonoid p.col]
    [Module ℝ p.col]
    (h_term_convex : ∀ S ∈ p.E, ConvexOn ℝ {Y : p.ι → p.col | p.feasible Y} (p.f S)) :
    ConvexOn ℝ {Y : p.ι → p.col | p.feasible Y} p.objective := by
  sorry

end «CAM-Bench-201»
