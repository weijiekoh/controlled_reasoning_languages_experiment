import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-303»

def euclideanLength {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (dotProduct x x)

structure SecondOrderConeProgram where
  n : ℕ
  k : ℕ
  c : Fin n → ℝ
  affineConstraints : Set (Fin n → ℝ)
  coneDim : Fin k → ℕ
  A : (i : Fin k) → Fin (coneDim i) → (Fin n → ℝ) → ℝ
  b : (i : Fin k) → Fin (coneDim i) → ℝ
  coneLinear : (i : Fin k) → Fin n → ℝ
  d : Fin k → ℝ

def SecondOrderConeProgram.objective (p : SecondOrderConeProgram) (z : Fin p.n → ℝ) : ℝ :=
  ∑ j, p.c j * z j
def SecondOrderConeProgram.coneLhs (p : SecondOrderConeProgram) (i : Fin p.k) (z : Fin p.n → ℝ) : ℝ :=
  euclideanLength (fun j : Fin (p.coneDim i) => p.A i j z + p.b i j)

def SecondOrderConeProgram.coneRhs (p : SecondOrderConeProgram) (i : Fin p.k) (z : Fin p.n → ℝ) : ℝ :=
  ∑ j, p.coneLinear i j * z j + p.d i

def SecondOrderConeProgram.IsFeasible (p : SecondOrderConeProgram) (z : Fin p.n → ℝ) : Prop :=
  z ∈ p.affineConstraints ∧ ∀ i : Fin p.k, p.coneLhs i z ≤ p.coneRhs i z

structure InfinityNormMinimization where
  n : ℕ
  m : ℕ
  A : Fin m → Fin n → ℝ
  b : Fin m → ℝ

def InfinityNormMinimization.isFeasible (p : InfinityNormMinimization) (x : Fin p.n → ℝ) : Prop :=
  ∀ i : Fin p.m, ∑ j, p.A i j * x j = p.b i

def InfinityNormMinimization.objective (p : InfinityNormMinimization) (x : Fin p.n → ℝ) : ℝ :=
  sInf {t : ℝ | ∀ i : Fin p.n, |x i| ≤ t}

structure ComplexInfinityNormSOCP where
  n : ℕ
  m : ℕ
  A_re : Fin m → Fin n → ℝ
  A_im : Fin m → Fin n → ℝ
  b_re : Fin m → ℝ
  b_im : Fin m → ℝ

def ComplexInfinityNormSOCP.isFeasible
    (p : ComplexInfinityNormSOCP) (xRe xIm : Fin p.n → ℝ) (t : ℝ) : Prop :=
  (∀ i : Fin p.m,
    ((∑ j : Fin p.n, (p.A_re i j * xRe j - p.A_im i j * xIm j)) = p.b_re i) ∧
    ((∑ j : Fin p.n, (p.A_re i j * xIm j + p.A_im i j * xRe j)) = p.b_im i)) ∧
  ∀ i : Fin p.n, Real.sqrt ((xRe i)^2 + (xIm i)^2) ≤ t

def ComplexInfinityNormSOCP.objective
    (p : ComplexInfinityNormSOCP) (xRe xIm : Fin p.n → ℝ) (t : ℝ) : ℝ :=
  t

theorem complex_infinity_norm_minimization_equivalent_to_socp_reformulation
    (m n : ℕ)
    (A_re A_im : Fin m → Fin n → ℝ)
    (b_re b_im : Fin m → ℝ)
    (h_mn : m < n)
    (h_full_row_rank :
      Function.Surjective
        (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
          (fun i : Fin m =>
            ∑ j : Fin n, (A_re i j * y.1 j - A_im i j * y.2 j),
           fun i : Fin m =>
            ∑ j : Fin n, (A_re i j * y.2 j + A_im i j * y.1 j))))
    (h_feasible :
      ∃ xRe xIm : Fin n → ℝ,
        ∀ i : Fin m,
          ((∑ j : Fin n, (A_re i j * xRe j - A_im i j * xIm j)) = b_re i) ∧
          ((∑ j : Fin n, (A_re i j * xIm j + A_im i j * xRe j)) = b_im i)) :
    let p : ComplexInfinityNormSOCP := {
      n := n
      m := m
      A_re := A_re
      A_im := A_im
      b_re := b_re
      b_im := b_im
    }

    ∀ xRe xIm : Fin n → ℝ,
      IsMinOn
        (fun xy : (Fin n → ℝ) × (Fin n → ℝ) =>
          iSup (fun i : Fin n => Real.sqrt ((xy.1 i)^2 + (xy.2 i)^2)))
        {xy |
          ∀ i : Fin m,
            (∑ j : Fin n, (A_re i j * xy.1 j - A_im i j * xy.2 j)) = b_re i ∧
            (∑ j : Fin n, (A_re i j * xy.2 j + A_im i j * xy.1 j)) = b_im i}
        (xRe, xIm) ↔
      (let t := iSup (fun i : Fin n => Real.sqrt ((xRe i)^2 + (xIm i)^2))
       p.isFeasible xRe xIm t ∧
       ∀ yRe yIm : Fin n → ℝ, ∀ s : ℝ, p.isFeasible yRe yIm s → t ≤ s) := by
  sorry

end «CAM-Bench-303»
