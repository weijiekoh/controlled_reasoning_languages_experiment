import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-621»

def partialMatrix (n : ℕ) (α : Type _) : Type _ :=
  Σ Ω : Set (Fin n × Fin n), Ω → α

def IsCompletion {n : ℕ} {α : Type _} (A : partialMatrix n α)
    (Acomp : Matrix (Fin n) (Fin n) α) : Prop :=
  ∀ p : Fin n × Fin n, ∀ hp : p ∈ A.1, Acomp p.1 p.2 = A.2 ⟨p, hp⟩

def IsPosDefCompletion {n : ℕ} (A : partialMatrix n ℝ)
    (Acomp : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsCompletion A Acomp ∧
    Acomp.IsSymm ∧
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Acomp.mulVec x)

def IsTridiagonal {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, 1 < Nat.dist i.1 j.1 → T i j = 0

theorem maxDet_posDefCompletion_has_tridiagonal_inverse
    {n : ℕ} (A : partialMatrix n ℝ)
    (hΩ : ∀ p : Fin n × Fin n, p ∈ A.1 ↔ Nat.dist p.1.1 p.2.1 ≤ 1)
    (Acomp : Matrix (Fin n) (Fin n) ℝ)
    (hcomp : IsPosDefCompletion A Acomp)
    (hmaxdet :
      ∀ B : Matrix (Fin n) (Fin n) ℝ,
        IsPosDefCompletion A B → B.det ≤ Acomp.det) :
    IsTridiagonal Acomp⁻¹ := by
  sorry

end «CAM-Bench-621»
