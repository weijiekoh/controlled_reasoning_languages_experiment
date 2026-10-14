import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-351»

def ellipsoid (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ‖A.mulVec (x - c)‖ ≤ 1}

structure CoveringEllipsoidTradeoffProblem (n : ℕ) where
  m : ℕ
  lambda : ℝ
  x : Fin m → (Fin n → ℝ)

def CoveringEllipsoidTradeoffProblem.slack
    {n : ℕ} (p : CoveringEllipsoidTradeoffProblem n)
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (i : Fin p.m) : ℝ :=
  max (‖A.mulVec (p.x i - c)‖ - 1) 0

def CoveringEllipsoidTradeoffProblem.objectiveFn
    {n : ℕ} (p : CoveringEllipsoidTradeoffProblem n)
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : ℝ :=
  -Real.log (Matrix.det A) + p.lambda * ∑ i : Fin p.m, CoveringEllipsoidTradeoffProblem.slack p A c i

def CoveringEllipsoidTradeoffProblem.is_feasible
    {n : ℕ} (p : CoveringEllipsoidTradeoffProblem n)
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  A.IsSymm ∧ A.PosDef

def CoveringEllipsoidTradeoffProblem.ellipsoid
    {n : ℕ} (p : CoveringEllipsoidTradeoffProblem n)
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | ‖A.mulVec (y - c)‖ ≤ 1}

theorem minkowskiFunctional_eq_norm_and_tradeoff_reformulation
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {c : Fin n → ℝ}
    (hA_symm : A.IsSymm) (hA_posDef : A.PosDef) :
    (∀ z : Fin n → ℝ,
      let M : (Fin n → ℝ) → Set (Fin n → ℝ) → ℝ :=
        fun z E => sInf {t : ℝ | 0 ≤ t ∧ z ∈ {y | ∃ x ∈ E, y = c + t • (x - c)}}
      M z (ellipsoid A c) = ‖A.mulVec (z - c)‖) ∧
    (∀ (p : CoveringEllipsoidTradeoffProblem n),
      1 ≤ p.m →
      0 < p.lambda →
      (-Real.log (Matrix.det A) +
          p.lambda * ∑ i : Fin p.m,
            max
              ((let M : (Fin n → ℝ) → Set (Fin n → ℝ) → ℝ :=
                  fun z E => sInf {t : ℝ | 0 ≤ t ∧ z ∈ {y | ∃ x ∈ E, y = c + t • (x - c)}}
                M (p.x i) (ellipsoid A c)) - 1)
              0) =
        CoveringEllipsoidTradeoffProblem.objectiveFn p A c) := by
  sorry

end «CAM-Bench-351»
