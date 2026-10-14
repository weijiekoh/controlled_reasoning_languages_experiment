import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-252»

open scoped BigOperators

structure PermutationMaximizationProblem where
  n : ℕ
  a : Fin n → ℝ

def PermutationMaximizationProblem.C (p : PermutationMaximizationProblem) : Set (Fin p.n → ℝ) :=
  {x | ∃ σ : Equiv.Perm (Fin p.n), x = fun i => p.a (σ i)}

def PermutationMaximizationProblem.dot (p : PermutationMaximizationProblem)
    (y x : Fin p.n → ℝ) : ℝ :=
  ∑ i, y i * x i

def PermutationMaximizationProblem.S_C (p : PermutationMaximizationProblem)
    (y : Fin p.n → ℝ) : ℝ :=
  (Finset.univ.image fun σ : Equiv.Perm (Fin p.n) => p.dot y (fun i => p.a (σ i))).max'
    ⟨p.dot y (fun i => p.a ((Equiv.refl (Fin p.n)) i)), by
      refine Finset.mem_image.mpr ?_
      exact ⟨Equiv.refl (Fin p.n), by simp, by simp⟩⟩

theorem permutationMaximizationProblem_S_C_eq_sum_sorted_mul_sorted
    (p : PermutationMaximizationProblem) (y : Fin p.n → ℝ) :
    ∃ e1 : Equiv.Perm (Fin p.n), ∃ e2 : Equiv.Perm (Fin p.n),
      (∀ i j : Fin p.n, i ≤ j → p.a (e1 i) ≥ p.a (e1 j)) ∧
      (∀ i j : Fin p.n, i ≤ j → y (e2 i) ≥ y (e2 j)) ∧
      p.S_C y =
        ∑ i : Fin p.n,
          (p.a ∘ e1) i * (y ∘ e2) i := by
  sorry

end «CAM-Bench-252»
