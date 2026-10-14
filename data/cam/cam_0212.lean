import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-212»

structure ResourceAllocationProblem where
  n : ℕ
  π : Fin n → ℝ
  U : ℝ → ℝ
  B : ℝ

def ResourceAllocationProblem.isFeasible (P : ResourceAllocationProblem) (x : Fin P.n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ Finset.univ.sum x = P.B

def ResourceAllocationProblem.objective (P : ResourceAllocationProblem) (x : Fin P.n → ℝ) : ℝ :=
  Finset.univ.sum fun i => P.π i * P.U (x i)

theorem resourceAllocation_equiv_convex_problem
    (n : ℕ)
    (a : Fin n → ℝ)
    (π : Fin n → ℝ)
    (B c : ℝ)
    (U : ℝ → ℝ)
    (ha : ∀ i, 0 < a i)
    (hπ_nonneg : ∀ i, 0 ≤ π i)
    (hπ_sum : Finset.univ.sum π = 1)
    (hB : 0 ≤ B)
    (hc0 : 0 < c)
    (hc1 : c < 1)
    (hU_concave : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun t => -U t)
    (hU_mono : Monotone U)
    (hU0 : U 0 = 0) :
    let P : ResourceAllocationProblem :=
      { n := n
        π := π
        U := fun p => U ((1 - c) * (Finset.univ.sum a + B) * p)
        B := B }
    (∀ x : Fin n → ℝ,
        P.isFeasible x →
        ∃ y : Fin n → ℝ,
          (∀ i, y i = x i / (x i + a i)) ∧
          (∀ i, 0 ≤ y i ∧ y i < 1) ∧
          Finset.univ.sum (fun i => a i * y i / (1 - y i)) = B ∧
          P.objective x = Finset.univ.sum (fun i => π i * U ((1 - c) * (Finset.univ.sum a + B) * y i))) ∧
    (∀ y : Fin n → ℝ,
        (∀ i, 0 ≤ y i ∧ y i < 1) →
        Finset.univ.sum (fun i => a i * y i / (1 - y i)) = B →
        ∃ x : Fin n → ℝ,
          P.isFeasible x ∧
          (∀ i, x i = a i * y i / (1 - y i)) ∧
          P.objective x = Finset.univ.sum (fun i => π i * U ((1 - c) * (Finset.univ.sum a + B) * y i))) := by
  sorry

end «CAM-Bench-212»
