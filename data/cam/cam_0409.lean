import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-409»

def ConvexConcave
    {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
    (X : Set E) (Y : Set F) (Φ : E → F → ℝ) : Prop :=
  (∀ y, y ∈ Y → ConvexOn ℝ X (fun x => Φ x y)) ∧
  (∀ x, x ∈ X → ConcaveOn ℝ Y (fun y => Φ x y))

def IsSaddlePoint
    {E F : Type*} [AddCommMonoid E] [Module ℝ E] [AddCommMonoid F] [Module ℝ F]
    (X : Set E) (Y : Set F) (Φ : E → F → ℝ) (xStar : E) (yStar : F) : Prop :=
  xStar ∈ X ∧ yStar ∈ Y ∧
    (∀ y, y ∈ Y → Φ xStar y ≤ Φ xStar yStar) ∧
    (∀ x, x ∈ X → Φ xStar yStar ≤ Φ x yStar)

def IsFeasible
    {ι E : Type*} (f : ι → E → ℝ) (S : Set ι) (w : E) : Prop :=
  ∀ i, i ∈ S → f i w ≤ 0

structure ConvexConcaveGame
    (n : ℕ) (nTilde : ℕ) (ι : Type*) (ιTilde : Type*) where
  objective : (Fin n → ℝ) → (Fin nTilde → ℝ) → ℝ
  wConstraint : ι → (Fin n → ℝ) → ℝ
  zConstraint : ιTilde → (Fin nTilde → ℝ) → ℝ
  wActiveSet : Set ι
  zActiveSet : Set ιTilde
  objective_convex_concave :
    ConvexConcave Set.univ Set.univ objective
  objective_differentiable :
    ∀ w z, DifferentiableAt ℝ (fun p : (Fin n → ℝ) × (Fin nTilde → ℝ) => objective p.1 p.2) (w, z)
  wConstraint_convex :
    ∀ i, i ∈ wActiveSet → ConvexOn ℝ Set.univ (wConstraint i)
  wConstraint_differentiable :
    ∀ i, i ∈ wActiveSet → ∀ w, DifferentiableAt ℝ (wConstraint i) w
  zConstraint_convex :
    ∀ i, i ∈ zActiveSet → ConvexOn ℝ Set.univ (zConstraint i)
  zConstraint_differentiable :
    ∀ i, i ∈ zActiveSet → ∀ z, DifferentiableAt ℝ (zConstraint i) z

def ConvexConcaveGame.wFeasible
    {n : ℕ} {nTilde : ℕ} {ι : Type*} {ιTilde : Type*}
    (G : ConvexConcaveGame n nTilde ι ιTilde) (w : Fin n → ℝ) : Prop :=
  IsFeasible G.wConstraint G.wActiveSet w

def ConvexConcaveGame.zFeasible
    {n : ℕ} {nTilde : ℕ} {ι : Type*} {ιTilde : Type*}
    (G : ConvexConcaveGame n nTilde ι ιTilde) (z : Fin nTilde → ℝ) : Prop :=
  IsFeasible G.zConstraint G.zActiveSet z

def ConvexConcaveGame.isSaddlePoint
    {n : ℕ} {nTilde : ℕ} {ι : Type*} {ιTilde : Type*}
    (G : ConvexConcaveGame n nTilde ι ιTilde)
    (w : Fin n → ℝ) (z : Fin nTilde → ℝ) : Prop :=
  IsSaddlePoint
    {w' | G.wFeasible w'}
    {z' | G.zFeasible z'}
    G.objective
    w
    z

theorem phi_t_convexConcave_of_barrier_terms
    {n : ℕ} {nTilde : ℕ} {ι : Type*} {ιTilde : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ιTilde] [DecidableEq ιTilde]
    (G : ConvexConcaveGame n nTilde ι ιTilde)
    (t : ℝ)
    (ht : 0 < t)
    (hwBarrier :
      ∀ i,
        ConvexOn ℝ
          {w | G.wFeasible w ∧ ∀ j, j ∈ G.wActiveSet → G.wConstraint j w < 0}
          (fun w => -Real.log (-G.wConstraint i w)))
    (hzBarrier :
      ∀ i,
        ConcaveOn ℝ
          {z | G.zFeasible z ∧ ∀ j, j ∈ G.zActiveSet → G.zConstraint j z < 0}
          (fun z => Real.log (-G.zConstraint i z))) :
    ConvexConcave
      {w | G.wFeasible w ∧ ∀ i, i ∈ G.wActiveSet → G.wConstraint i w < 0}
      {z | G.zFeasible z ∧ ∀ i, i ∈ G.zActiveSet → G.zConstraint i z < 0}
      (fun w z =>
        t * G.objective w z
          - ∑ i : ι, Real.log (-G.wConstraint i w)
          + ∑ i : ιTilde, Real.log (-G.zConstraint i z)) := by
  sorry

end «CAM-Bench-409»
