import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-399»

def newtonStep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hess : E → E →L[ℝ] E)
    (grad : E → E)
    (x : E)
    (hInv : E →L[ℝ] E)
    (_h_left : hInv.comp (hess x) = ContinuousLinearMap.id ℝ E)
    (_h_right : (hess x).comp hInv = ContinuousLinearMap.id ℝ E) : E :=
  -(hInv (grad x))

def isRankOneModification
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℝ) : Prop :=
  ∃ u : m → ℝ, ∃ v : n → ℝ, B = A + Matrix.vecMulVec u v

structure SeparableEqualityConstrainedProblem where
  n : ℕ
  hn : 1 ≤ n
  f : Fin n → ℝ → ℝ
  h_twiceContDiff : ∀ i : Fin n, ContDiff ℝ 2 (f i)
  m : ℝ
  hm : 0 < m
  h_strong_convex :
    ∀ i : Fin n, ∀ z : ℝ, m ≤ deriv (deriv (f i)) z

def SeparableEqualityConstrainedProblem.reducedObjective
    (P : SeparableEqualityConstrainedProblem) : (Fin (P.n - 1) → ℝ) → ℝ :=
  fun z : Fin (P.n - 1) → ℝ =>
    let last : Fin P.n := ⟨P.n - 1, by
      have hn' : 0 < P.n := Nat.lt_of_lt_of_le (Nat.succ_pos 0) P.hn
      exact Nat.sub_lt hn' (by simp)⟩
    (∑ i : Fin (P.n - 1),
      P.f ⟨i.1, Nat.lt_trans i.2
        (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) P.hn) (by simp))⟩ (z i)) +
      P.f last (1 - ∑ j : Fin (P.n - 1), z j)

def SeparableEqualityConstrainedProblem.objective
    (P : SeparableEqualityConstrainedProblem) (x : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, P.f i (x i)

def SeparableEqualityConstrainedProblem.feasible
    (P : SeparableEqualityConstrainedProblem) (x : Fin P.n → ℝ) : Prop :=
  (∑ i : Fin P.n, x i) = 1

theorem reducedProblem_newtonStep_linear_system_and_rank_one_cost
    (P : SeparableEqualityConstrainedProblem)
    (z : Fin (P.n - 1) → ℝ)
    (reducedHess : (Fin (P.n - 1) → ℝ) → ((Fin (P.n - 1) → ℝ) →ₗ[ℝ] (Fin (P.n - 1) → ℝ)))
    (reducedGrad : (Fin (P.n - 1) → ℝ) → (Fin (P.n - 1) → ℝ))
    (reducedHessInv : ((Fin (P.n - 1) → ℝ) →ₗ[ℝ] (Fin (P.n - 1) → ℝ)))
    (h_hess :
      reducedHess z =
        (Matrix.toLin'
          (let D : Matrix (Fin (P.n - 1)) (Fin (P.n - 1)) ℝ :=
            Matrix.diagonal
              (fun i : Fin (P.n - 1) =>
                deriv
                  (deriv
                    (P.f
                      ⟨i, Nat.lt_trans i.2
                        (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) P.hn) (by simp))⟩))
                  (z i))
          let d : ℝ :=
            deriv
              (deriv (P.f ⟨P.n - 1, Nat.pred_lt (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) P.hn))⟩))
              (1 - ∑ j : Fin (P.n - 1), z j)
          D + d • Matrix.vecMulVec (fun _ : Fin (P.n - 1) => (1 : ℝ)) (fun _ : Fin (P.n - 1) => (1 : ℝ)))))
    (h_left :
      reducedHessInv.comp (reducedHess z) =
        LinearMap.id)
    (h_right :
      (reducedHess z).comp reducedHessInv =
        LinearMap.id) :
    let D : Matrix (Fin (P.n - 1)) (Fin (P.n - 1)) ℝ :=
      Matrix.diagonal
        (fun i : Fin (P.n - 1) =>
          deriv
            (deriv
              (P.f
                ⟨i, Nat.lt_trans i.2
                  (Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) P.hn) (by simp))⟩))
            (z i))
    let d : ℝ :=
      deriv
        (deriv (P.f ⟨P.n - 1, Nat.pred_lt (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) P.hn))⟩))
        (1 - ∑ j : Fin (P.n - 1), z j)
    let g : Fin (P.n - 1) → ℝ :=
      reducedGrad z
    let reducedHessMatrix : Matrix (Fin (P.n - 1)) (Fin (P.n - 1)) ℝ :=
      D + d • Matrix.vecMulVec (fun _ : Fin (P.n - 1) => (1 : ℝ)) (fun _ : Fin (P.n - 1) => (1 : ℝ))
    let δz : Fin (P.n - 1) → ℝ :=
      -(reducedHessInv (reducedGrad z))
    D.IsDiag ∧
    isRankOneModification D reducedHessMatrix ∧
    (reducedHessMatrix.mulVec δz = fun i => -g i) ∧
    ∃ C : ℕ, (P.n - 1) ≤ C * P.n + C := by
  intro D d g reducedHessMatrix δz
  refine ⟨Matrix.isDiag_diagonal _, ⟨fun _ => d, fun _ => 1, ?_⟩, ?_, ⟨P.n, ?_⟩⟩
  · ext i j
    simp [reducedHessMatrix, Matrix.vecMulVec, Matrix.smul_apply]
  · have hy : reducedHessMatrix.mulVec (reducedHessInv (reducedGrad z)) = reducedGrad z := by
      have h := congrArg (fun L => L (reducedGrad z)) h_right
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
      rw [h_hess, Matrix.toLin'_apply] at h
      exact h
    show reducedHessMatrix.mulVec (-(reducedHessInv (reducedGrad z))) = fun i => -(reducedGrad z) i
    rw [Matrix.mulVec_neg, hy]
    rfl
  · exact le_trans (Nat.sub_le _ _) (Nat.le_add_left _ _)

end «CAM-Bench-399»
