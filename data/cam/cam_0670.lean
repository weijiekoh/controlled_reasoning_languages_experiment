import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-670»

namespace Exercise_7_11

def ColumnStochastic {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i k, 0 ≤ T i k) ∧ ∀ k, ∑ i : Fin m, T i k = 1

def deterministicMatrix {m n : ℕ} (α : Fin n → Fin m) : Matrix (Fin m) (Fin n) ℝ :=
  fun i k => if i = α k then 1 else 0

def theta {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (α : Fin n → Fin m) : ℝ :=
  ∏ k : Fin n, T (α k) k

theorem columnStochastic_is_convexCombination_of_deterministic
    {m n : ℕ} (T : Matrix (Fin m) (Fin n) ℝ) (hT : ColumnStochastic T) :
    (∀ α : Fin n → Fin m, 0 ≤ theta T α) ∧
    (∑ α : (Fin n → Fin m), theta T α = 1) ∧
    (T = ∑ α : (Fin n → Fin m), (theta T α) • deterministicMatrix α) := by
  sorry
end Exercise_7_11

end «CAM-Bench-670»
