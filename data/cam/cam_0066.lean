import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-66»

def activeSet {ι : Type*} (equalities inequalities : Set ι) (a : ι → Fin n → ℝ) (b : ι → ℝ)
    (x : Fin n → ℝ) : Set ι :=
  equalities ∪ {i | i ∈ inequalities ∧ ∑ j, a i j * x j = b i}

def feasiblePoint {n : ℕ} {ι : Type*} (equalities inequalities : Set ι) (a : ι → Fin n → ℝ)
    (b : ι → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i, i ∈ equalities → ∑ j, a i j * x j = b i) ∧
    ∀ i, i ∈ inequalities → ∑ j, a i j * x j ≥ b i

def multiplier (ι : Type*) := ι → ℝ

def isGlobalSolution {n : ℕ} {ι : Type*} (f : (Fin n → ℝ) → ℝ) (equalities inequalities : Set ι)
    (a : ι → Fin n → ℝ) (b : ι → ℝ) (xStar : Fin n → ℝ) : Prop :=
  feasiblePoint equalities inequalities a b xStar ∧
    ∀ x, feasiblePoint equalities inequalities a b x → f xStar ≤ f x

def isUniqueGlobalSolution {n : ℕ} {ι : Type*} (f : (Fin n → ℝ) → ℝ) (equalities inequalities : Set ι)
    (a : ι → Fin n → ℝ) (b : ι → ℝ) (xStar : Fin n → ℝ) : Prop :=
  feasiblePoint equalities inequalities a b xStar ∧
    ∀ x, feasiblePoint equalities inequalities a b x → x ≠ xStar → f xStar < f x

structure ConvexQuadraticProgram (n : ℕ) (ι : Type*) where
  G : Matrix (Fin n) (Fin n) ℝ
  c : Fin n → ℝ
  equalities : Set ι
  inequalities : Set ι
  a : ι → Fin n → ℝ
  b : ι → ℝ
  G_symmetric : G.IsSymm
  G_posSemidef : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, x i * G i j * x j

def ConvexQuadraticProgram.objective {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, x i * P.G i j * x j + ∑ i, P.c i * x i

def ConvexQuadraticProgram.isFeasible {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : Prop :=
  feasiblePoint P.equalities P.inequalities P.a P.b x

def ConvexQuadraticProgram.activeSet {n : ℕ} {ι : Type*} (P : ConvexQuadraticProgram n ι)
    (x : Fin n → ℝ) : Set ι :=
  {i | i ∈ P.inequalities ∧ ∑ j, P.a i j * x j = P.b i}

theorem unique_global_solution_of_kkt_activeSet_posDef
    {n : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (P : ConvexQuadraticProgram n ι) (xStar : Fin n → ℝ) (Z : κ → Fin n → ℝ)
    (lam : multiplier ι)
    (hxFeas : P.isFeasible xStar)
    (hlam_support : ∀ i, i ∉ activeSet P.equalities P.inequalities P.a P.b xStar → lam i = 0)
    (hstationary :
      ∀ j, ∑ i, lam i * P.a i j = ∑ k, P.G j k * xStar k + P.c j)
    (hactive_eq :
      ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * xStar j = P.b i)
    (hZbasis :
      (∀ d : Fin n → ℝ,
        (∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar → ∑ j, P.a i j * d j = 0) →
        ∃ mu : κ → ℝ, d = fun j => ∑ i, Z i j * mu i) ∧
      (∀ mu : κ → ℝ,
        ∀ i, i ∈ activeSet P.equalities P.inequalities P.a P.b xStar →
          ∑ j, P.a i j * (∑ k, Z k j * mu k) = 0) ∧
      (∀ mu : κ → ℝ,
        (∀ j, (∑ i, Z i j * mu i) = 0) →
        mu = 0))
    (hposdef :
      ∀ mu : κ → ℝ, mu ≠ 0 →
        0 < ∑ j, ∑ k, (∑ i, Z i j * mu i) * P.G j k * (∑ i, Z i k * mu i)) :
    isUniqueGlobalSolution P.objective P.equalities P.inequalities P.a P.b xStar := by
  sorry

end «CAM-Bench-66»
