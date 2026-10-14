import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-630»

structure SingleConstraintLinearProgram (n : ℕ) where
  a : Fin n → ℝ
  c : Fin n → ℝ
  b : ℝ
  a_ne_zero : a ≠ 0

def SingleConstraintLinearProgram.isFeasible {n : ℕ}
    (P : SingleConstraintLinearProgram n) (x : Fin n → ℝ) : Prop :=
  ∑ i, P.a i * x i ≤ P.b

def SingleConstraintLinearProgram.objective {n : ℕ}
    (P : SingleConstraintLinearProgram n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, P.c i * x i

theorem singleConstraintLinearProgram_dualAlternative
    (n : ℕ) (P : SingleConstraintLinearProgram n) :
    (∃ x : Fin n → ℝ, P.isFeasible x) ∧
      (let case1 :=
        ∃ lam : ℝ,
          P.c = lam • P.a ∧ lam ≤ 0 ∧
            (sInf {v : ℝ | ∃ x : Fin n → ℝ, P.isFeasible x ∧ P.objective x = v} = lam * P.b) ∧
            (∀ x : Fin n → ℝ,
              P.isFeasible x →
                (∑ i, P.a i * x i = P.b) →
                  P.objective x = lam * P.b)
      let case2 :=
        (¬ ∃ lam : ℝ, P.c = lam • P.a ∧ lam ≤ 0) ∧
          (∀ M : ℝ, ∃ x : Fin n → ℝ, P.isFeasible x ∧ P.objective x < M)
      (case1 ∨ case2) ∧ ¬ (case1 ∧ case2)) := by
  sorry

end «CAM-Bench-630»
