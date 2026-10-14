import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-726»

structure KMeansClusteringProblem (n m k : ℕ) where
  points : Fin n → EuclideanSpace ℝ (Fin m)
  clusters : Fin k → Finset (Fin n)
  nonempty : ∀ t : Fin k, 0 < (clusters t).card
  pairwiseDisjoint : Pairwise fun i j : Fin k => Disjoint (clusters i) (clusters j)
  cover : Finset.biUnion Finset.univ clusters = Finset.univ

def KMeansClusteringProblem.indicatorVector {n m k : ℕ}
    (_P : KMeansClusteringProblem n m k) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then 1 else 0

def KMeansClusteringProblem.distanceMatrix {n m k : ℕ} (P : KMeansClusteringProblem n m k) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ‖P.points i - P.points j‖ ^ 2

def KMeansClusteringProblem.assignmentMatrix {n m k : ℕ} (P : KMeansClusteringProblem n m k) :
    Matrix (Fin n) (Fin n) ℝ :=
  ∑ t : Fin k,
    ((P.clusters t).card : ℝ)⁻¹ •
      Matrix.vecMulVec (P.indicatorVector (P.clusters t)) (P.indicatorVector (P.clusters t))

def KMeansClusteringProblem.objectiveValue {n m k : ℕ} (P : KMeansClusteringProblem n m k) : ℝ :=
  (1 / 2 : ℝ) * Matrix.trace (P.distanceMatrix * P.assignmentMatrix)

def KMeansClusteringProblem.isFeasible {n m k : ℕ} (P : KMeansClusteringProblem n m k) : Prop :=
  (∀ t : Fin k, 0 < (P.clusters t).card) ∧
    Pairwise (fun i j : Fin k => Disjoint (P.clusters i) (P.clusters j)) ∧
    Finset.biUnion Finset.univ P.clusters = Finset.univ

theorem KMeansClusteringProblem.assignmentMatrixIsPSD {n m k : ℕ}
    (P : KMeansClusteringProblem n m k) :
    Matrix.PosSemidef P.assignmentMatrix := by
  sorry

end «CAM-Bench-726»
