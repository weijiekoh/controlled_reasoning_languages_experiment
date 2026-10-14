import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-711»

structure TraceMinimizationSDPData (n m : Type) [Fintype n] [Fintype m] where
  A : Matrix m m ℝ
  B : Matrix m n ℝ

structure TraceMinimizationSDP (n m : Type) [Fintype n] [Fintype m] where
  data : TraceMinimizationSDPData n m
  decision : {X : Matrix n n ℝ // X.IsSymm}

def TraceMinimizationSDP.A {n m : Type} [Fintype n] [Fintype m]
    (P : TraceMinimizationSDP n m) : Matrix m m ℝ :=
  P.data.A

def TraceMinimizationSDP.B {n m : Type} [Fintype n] [Fintype m]
    (P : TraceMinimizationSDP n m) : Matrix m n ℝ :=
  P.data.B

def TraceMinimizationSDP.X {n m : Type} [Fintype n] [Fintype m]
    (P : TraceMinimizationSDP n m) : Matrix n n ℝ :=
  P.decision.1

def TraceMinimizationSDP.feasible {n m : Type} [Fintype n] [Fintype m]
    (P : TraceMinimizationSDP n m) : Prop :=
  Matrix.PosSemidef (Matrix.fromBlocks P.A P.B P.B.transpose P.X)

def TraceMinimizationSDP.objective {n m : Type} [Fintype n] [Fintype m]
    (P : TraceMinimizationSDP n m) : ℝ :=
  Matrix.trace P.X

def TraceMinimizationSDP.is_feasible {n m : Type} [Fintype n] [Fintype m]
    (P : TraceMinimizationSDP n m) : Prop :=
  P.feasible

theorem traceMinimizationSDP_optimal_solution_eq
    {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hA_symm : A.IsSymm)
    (hA_pos : Matrix.PosDef A)
    (X : Matrix n n ℝ)
    (hX_symm : X.IsSymm)
    (h_feas : Matrix.PosSemidef (Matrix.fromBlocks A B B.transpose X))
    (h_opt :
      ∀ Y : Matrix n n ℝ,
        Y.IsSymm →
        Matrix.PosSemidef (Matrix.fromBlocks A B B.transpose Y) →
        Matrix.trace X ≤ Matrix.trace Y)
    (h_ref_symm : (Bᵀ * (A⁻¹ * B)).IsSymm)
    (h_ref_feas :
      Matrix.PosSemidef (Matrix.fromBlocks A B B.transpose (Bᵀ * (A⁻¹ * B))))
    (h_opt_unique :
      ∀ Y : Matrix n n ℝ,
        Y.IsSymm →
        Matrix.PosSemidef (Matrix.fromBlocks A B B.transpose Y) →
        Matrix.trace Y = Matrix.trace X →
        Y = X) :
    X = Bᵀ * (A⁻¹ * B) := by
  sorry

end «CAM-Bench-711»
