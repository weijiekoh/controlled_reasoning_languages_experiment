import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-302»

structure LeastL2NormProblem where
  m : Type
  n : Type
  [instDecidableEqM : DecidableEq m]
  [instFintypeM : Fintype m]
  [instDecidableEqN : DecidableEq n]
  [instFintypeN : Fintype n]
  A : Matrix m n ℝ
  b : m → ℝ

attribute [instance] LeastL2NormProblem.instDecidableEqM
attribute [instance] LeastL2NormProblem.instFintypeM
attribute [instance] LeastL2NormProblem.instDecidableEqN
attribute [instance] LeastL2NormProblem.instFintypeN

def LeastL2NormProblem.objective (p : LeastL2NormProblem) (x : p.n → ℝ) : ℝ :=
  ‖x‖

def LeastL2NormProblem.isFeasible (p : LeastL2NormProblem) (x : p.n → ℝ) : Prop :=
  p.A.mulVec x = p.b

structure ComplexLeastL2NormProblem where
  m : Type
  n : Type
  [instDecidableEqM : DecidableEq m]
  [instFintypeM : Fintype m]
  [instDecidableEqN : DecidableEq n]
  [instFintypeN : Fintype n]
  A : Matrix m n ℂ
  b : m → ℂ

attribute [instance] ComplexLeastL2NormProblem.instDecidableEqM
attribute [instance] ComplexLeastL2NormProblem.instFintypeM
attribute [instance] ComplexLeastL2NormProblem.instDecidableEqN
attribute [instance] ComplexLeastL2NormProblem.instFintypeN

def ComplexLeastL2NormProblem.realificationA
    (p : ComplexLeastL2NormProblem) :
    Matrix (Sum p.m p.m) (Sum p.n p.n) ℝ :=
  fun i j =>
    match i, j with
    | Sum.inl im, Sum.inl jn => Complex.re (p.A im jn)
    | Sum.inl im, Sum.inr jn => -Complex.im (p.A im jn)
    | Sum.inr im, Sum.inl jn => Complex.im (p.A im jn)
    | Sum.inr im, Sum.inr jn => Complex.re (p.A im jn)

def ComplexLeastL2NormProblem.realificationb
    (p : ComplexLeastL2NormProblem) : Sum p.m p.m → ℝ :=
  fun i =>
    match i with
    | Sum.inl im => Complex.re (p.b im)
    | Sum.inr im => Complex.im (p.b im)

def ComplexLeastL2NormProblem.toReal
    (p : ComplexLeastL2NormProblem) (x : p.n → ℂ) :
    Sum p.n p.n → ℝ :=
  fun j =>
    match j with
    | Sum.inl k => Complex.re (x k)
    | Sum.inr k => Complex.im (x k)

def ComplexLeastL2NormProblem.toComplex
    (p : ComplexLeastL2NormProblem) (z : Sum p.n p.n → ℝ) : p.n → ℂ :=
  fun k => (z (Sum.inl k) : ℂ) + Complex.I * (z (Sum.inr k) : ℂ)

theorem complex_least_l2_norm_equiv_realification
    (p : ComplexLeastL2NormProblem) :
    (∀ x : p.n → ℂ,
      p.A.mulVec x = p.b ↔
        (fun i : Sum p.m p.m =>
          ∑ j : Sum p.n p.n, p.realificationA i j * p.toReal x j) =
            p.realificationb) ∧
    (∀ x : p.n → ℂ,
      Real.sqrt (∑ k, (Complex.normSq (x k))) =
        Real.sqrt (∑ j : Sum p.n p.n, (p.toReal x j) ^ 2)) := by
  sorry

end «CAM-Bench-302»
