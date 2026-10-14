import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-318»

structure RobustLinearProgram (m n p : ℕ) where
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  uncertaintySet : Set (Fin p → ℝ)
  uncertainA : (Fin p → ℝ) → Fin m → Fin n → ℝ
  uncertainb : (Fin p → ℝ) → Fin m → ℝ
  uncertainc : (Fin p → ℝ) → Fin n → ℝ

def RobustLinearProgram.isFeasible {m n p : ℕ} (P : RobustLinearProgram m n p) (x : Fin n → ℝ) : Prop :=
  ∀ u ∈ P.uncertaintySet, ∀ i : Fin m, (∑ j : Fin n, P.uncertainA u i j * x j) ≤ P.uncertainb u i

def RobustLinearProgram.objectiveValue {m n p : ℕ} (P : RobustLinearProgram m n p) (x : Fin n → ℝ) : Set ℝ :=
  {t | ∀ u ∈ P.uncertaintySet, t = ∑ j : Fin n, P.uncertainc u j * x j}

theorem inf_supportFunction_eq_inf_reformulatedLinearProgram
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (F : Fin p → Fin n → ℝ)
    (g : Fin p → ℝ)
    (C : Set (Fin n → ℝ))
    (hC : C = {c | ∀ k : Fin p, ∑ j : Fin n, F k j * c j ≤ g k})
    (hC_nonempty : C.Nonempty)
    (hAx_nonempty : ∃ x : Fin n → ℝ, ∀ i : Fin m, b i ≤ ∑ j : Fin n, A i j * x j)
    (f : (Fin n → ℝ) → EReal)
    (hf_support :
      ∀ x : Fin n → ℝ,
        f x =
          sSup
            {t : EReal |
              ∃ c ∈ C, t = (∑ j : Fin n, ((c j : ℝ) : EReal) * ((x j : ℝ) : EReal))})
    (hf :
      ∀ x : Fin n → ℝ,
        (∃ y : Fin p → ℝ,
            (∀ k : Fin p, 0 ≤ y k) ∧
            (∀ j : Fin n, ∑ k : Fin p, F k j * y k = x j)) →
          f x =
            sInf
              {t : EReal |
                ∃ y : Fin p → ℝ,
                  (∀ k : Fin p, 0 ≤ y k) ∧
                  (∀ j : Fin n, ∑ k : Fin p, F k j * y k = x j) ∧
                  t = (∑ k : Fin p, (g k : EReal) * (y k : EReal))})
    (hf_top :
      ∀ x : Fin n → ℝ,
        (¬ ∃ y : Fin p → ℝ,
            (∀ k : Fin p, 0 ≤ y k) ∧
            (∀ j : Fin n, ∑ k : Fin p, F k j * y k = x j)) →
          f x = ⊤) :
    sInf {t : EReal |
      ∃ x : Fin n → ℝ,
        (∀ i : Fin m, b i ≤ ∑ j : Fin n, A i j * x j) ∧
        t = f x} =
    sInf {t : EReal |
      ∃ y : Fin p → ℝ,
        (∀ k : Fin p, 0 ≤ y k) ∧
        (∀ i : Fin m, b i ≤ ∑ j : Fin n, A i j * (∑ k : Fin p, F k j * y k)) ∧
        t = (∑ k : Fin p, (g k : EReal) * (y k : EReal))} := by
  sorry

end «CAM-Bench-318»
