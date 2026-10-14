import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-306»

structure LinearProgram (m n p : ℕ) where
  c : Fin n → ℝ
  G : Matrix (Fin m) (Fin n) ℝ
  h : Fin m → ℝ
  E : Matrix (Fin p) (Fin n) ℝ
  d : Fin p → ℝ

def LinearProgram.objective {m n p : ℕ} (P : LinearProgram m n p) (x : Fin n → ℝ) : ℝ :=
  dotProduct P.c x

def LinearProgram.IsFeasible {m n p : ℕ} (P : LinearProgram m n p) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, (P.G.mulVec x) i ≤ P.h i) ∧ (P.E.mulVec x = P.d)

def ComponentwiseGE {m : ℕ} (u v : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, v i ≤ u i

def ComplementarySlackness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (b y : Fin m → ℝ) : Prop :=
  (∀ i : Fin m, 0 ≤ y i) ∧ ∀ i : Fin m, y i * ((A.mulVec x) i - b i) = 0

def DualFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  ComponentwiseGE y 0 ∧ A.transpose.mulVec y = c

def PrimalFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  ComponentwiseGE (A.mulVec x) b

structure LinearProgramWithUnknownCost (m n : ℕ) where
  A : Matrix (Fin m) (Fin n) ℝ
  b : Fin m → ℝ

def LinearProgramWithUnknownCost.isFeasible {m n : ℕ} (P : LinearProgramWithUnknownCost m n)
    (x : Fin n → ℝ) : Prop :=
  PrimalFeasible P.A P.b x

def LinearProgramWithUnknownCost.objective {m n : ℕ} (P : LinearProgramWithUnknownCost m n)
    (c x : Fin n → ℝ) : ℝ :=
  dotProduct c x

theorem exists_common_cost_vector_iff_exists_dual_certificates
    {m n r : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin r → Fin m → ℝ) (x : Fin r → Fin n → ℝ) :
    (∃ c : Fin n → ℝ,
      ∀ j : Fin r,
        PrimalFeasible A (b j) (x j) ∧
        ∀ z : Fin n → ℝ, PrimalFeasible A (b j) z → dotProduct c (x j) ≤ dotProduct c z) ↔
    ∃ y : Fin r → Fin m → ℝ,
      (∀ j : Fin r, PrimalFeasible A (b j) (x j)) ∧
      (∀ j : Fin r, ComponentwiseGE (y j) 0) ∧
      (∀ j1 j2 : Fin r, A.transpose.mulVec (y j1) = A.transpose.mulVec (y j2)) ∧
      (∀ j : Fin r, ComplementarySlackness A (x j) (b j) (y j)) := by
  sorry

end «CAM-Bench-306»
