import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-634»

def weakMaxMinInequality {W Z : Type*} (f : W → Z → ℝ) : Prop :=
  sSup (Set.range fun z : Z => sInf (Set.range fun w : W => f w z)) ≤
    sInf (Set.range fun w : W => sSup (Set.range fun z : Z => f w z))

theorem weak_max_min_inequality_holds
    {n m : ℕ} (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ) → EReal) :
    sSup (Set.range fun z : Z => sInf (Set.range fun w : W => f w.1 z.1)) ≤
      sInf (Set.range fun w : W => sSup (Set.range fun z : Z => f w.1 z.1)) := by
  sorry

end «CAM-Bench-634»
