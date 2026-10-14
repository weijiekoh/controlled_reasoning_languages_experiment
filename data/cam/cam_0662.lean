import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-662»

def IsQuasiconvexOptimizationProblem {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → ℝ) (C : Set E) : Prop :=
  QuasiconvexOn ℝ C f ∧ Convex ℝ C

def IsQuasiconvexFunction {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → EReal) : Prop :=
  ∀ α : ℝ, Convex ℝ {x : E | f x ≤ (α : EReal)}

structure LengthMinimizationProblem (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ
  ε : ℝ
  norm : Seminorm ℝ (Fin m → ℝ)
  norm_pos : ∀ x : Fin m → ℝ, 0 ≤ norm x
  norm_eq_zero : ∀ x : Fin m → ℝ, norm x = 0 ↔ x = 0
  epsilon_pos : 0 < ε

def LengthMinimizationProblem.feasible {m n : ℕ} (P : LengthMinimizationProblem m n)
    (x : Fin n → ℝ) : Prop :=
  P.norm (fun i => (P.A.mulVec x) i - P.b i) ≤ P.ε

def LengthMinimizationProblem.objective {m n : ℕ} (_P : LengthMinimizationProblem m n)
    (x : Fin n → ℝ) : ℕ :=
  let nz : Finset ℕ := (Finset.univ.filter (fun i : Fin n => x i ≠ 0)).image (fun i => i.1 + 1)
  if h : nz.Nonempty then nz.max' h else 0

theorem lengthMinimizationProblem_isQuasiconvexOptimizationProblem (m n : ℕ)
    (P : LengthMinimizationProblem m n)
    (hnorm :
      ∀ u v : Fin m → ℝ, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        P.norm (fun i => a * u i + b * v i) ≤ a * P.norm u + b * P.norm v) :
    IsQuasiconvexOptimizationProblem
      (fun x : Fin n → ℝ => (LengthMinimizationProblem.objective P x : ℝ))
      {x : Fin n → ℝ | LengthMinimizationProblem.feasible P x} := by
  sorry

end «CAM-Bench-662»
