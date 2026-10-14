import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-546»

open scoped Real

def convexConjugate {m : ℕ} (f : (Fin m → ℝ) → EReal) : (Fin m → ℝ) → EReal :=
  fun y => sSup (Set.range fun x : Fin m → ℝ => ((∑ i, y i * x i : ℝ) : EReal) - f x)

theorem convexConjugate_trace_inv_eq_negTwo_trace_sqrt
    {n : Type} [Fintype n] [DecidableEq n] :
    (∀ Y : Matrix n n ℝ, ∀ hY : (-Y).PosSemidef,
      sSup (Set.range fun X : {X : Matrix n n ℝ // X.PosDef} =>
        (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) =
        (((-2 : ℝ) * Matrix.trace (Matrix.PosSemidef.sqrt hY)) : EReal)) ∧
    ({Y : Matrix n n ℝ |
      sSup (Set.range fun X : {X : Matrix n n ℝ // X.PosDef} =>
        (((Matrix.trace (Y * X.1)) : ℝ) : EReal) -
          (((Matrix.trace (X.1⁻¹)) : ℝ) : EReal)) < ⊤} =
      {Y : Matrix n n ℝ | (-Y).PosSemidef}) := by
  sorry

end «CAM-Bench-546»
