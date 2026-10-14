import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-311»

structure SemidefiniteProgram (n p : ℕ) where
  F : Fin (p + 1) → Matrix (Fin n) (Fin n) ℝ
  c : Fin p → ℝ

def SemidefiniteProgram.lmiMatrix {n p : ℕ} (S : SemidefiniteProgram n p) (y : Fin p → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  S.F 0 + ∑ i : Fin p, y i • S.F i.succ

def SemidefiniteProgram.IsFeasible {n p : ℕ} (S : SemidefiniteProgram n p) (y : Fin p → ℝ) :
    Prop :=
  Matrix.PosSemidef (S.lmiMatrix y)

def SemidefiniteProgram.objective {n p : ℕ} (S : SemidefiniteProgram n p) (y : Fin p → ℝ) :
    ℝ :=
  ∑ i : Fin p, S.c i * y i

structure TraceHeuristicSDP (n m : ℕ) where
  r : ℝ
  A : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ

def TraceHeuristicSDP.slackMatrix {n m : ℕ} (P : TraceHeuristicSDP n m)
    (x : Fin m → ℝ) (z : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Z + z • (1 : Matrix (Fin n) (Fin n) ℝ) - P.A 0 - ∑ i : Fin m, x i • P.A i.succ

def TraceHeuristicSDP.objective {n m : ℕ} (P : TraceHeuristicSDP n m)
    (z : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  P.r * z + Matrix.trace Z

def TraceHeuristicSDP.feasible {n m : ℕ} (P : TraceHeuristicSDP n m)
    (x : Fin m → ℝ) (z : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z.PosSemidef ∧ (P.slackMatrix x z Z).PosSemidef

def TraceHeuristicSDP.objectiveValue {n m : ℕ} (P : TraceHeuristicSDP n m)
    (z : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  P.objective z Z

def TraceHeuristicSDP.IsFeasible {n m : ℕ} (P : TraceHeuristicSDP n m)
    (x : Fin m → ℝ) (z : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.feasible x z Z

theorem min_sum_top_eigenvalues_equiv_trace_heuristic_sdp
    {n m r : ℕ} (hr : 1 ≤ r ∧ r ≤ n) (P : TraceHeuristicSDP n m)
    (hPr : P.r = r)
    (f : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hf :
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        f A =
          sInf
            {t : ℝ |
              ∃ z : ℝ,
                ∃ Z : Matrix (Fin n) (Fin n) ℝ,
                  Z.PosSemidef ∧
                    (Z + z • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef ∧
                    t = r * z + Matrix.trace Z}) :
    {v : ℝ | ∃ x : Fin m → ℝ, v = f (P.A 0 + ∑ i : Fin m, x i • P.A i.succ)} =
      {v : ℝ |
        ∃ x : Fin m → ℝ,
          ∃ z : ℝ,
            ∃ Z : Matrix (Fin n) (Fin n) ℝ,
              TraceHeuristicSDP.IsFeasible P x z Z ∧
                v = TraceHeuristicSDP.objective P z Z} := by
  sorry

end «CAM-Bench-311»
