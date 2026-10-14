import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-654»

def ChebyshevScalarApproximation {n : ℕ} (b : Fin n → ℝ) : Set ℝ :=
  {x : ℝ | ∀ y : ℝ, sSup (Set.range fun i : Fin n => |x - b i|) ≤ sSup (Set.range fun i : Fin n => |y - b i|)}

def ChebyshevScalarApproximation.objective
    {n : ℕ} (b : Fin n → ℝ) (x : ℝ) : ℝ :=
  sSup (Set.range fun i : Fin n => |x - b i|)

def ChebyshevScalarApproximation.isMinimizer
    {n : ℕ} (b : Fin n → ℝ) (x : ℝ) : Prop :=
  x ∈ ChebyshevScalarApproximation b

variable (x : ℝ)

theorem chebyshevScalarApproximation_minimizers_eq_midrange
    {n : ℕ} [Fact (0 < n)]
    (b : Fin n → ℝ)
    (x : ℝ) :
    (ChebyshevScalarApproximation.isMinimizer b x) ↔
      x = ((Finset.univ.sup' (by
        classical
        exact ⟨⟨0, Fact.out⟩, by simp⟩) b) +
        (Finset.univ.inf' (by
        classical
        exact ⟨⟨0, Fact.out⟩, by simp⟩) b)) / 2 := by
  sorry

end «CAM-Bench-654»
