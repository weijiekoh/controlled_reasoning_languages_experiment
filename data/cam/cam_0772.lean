import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-772»

open scoped BigOperators

def proximalOperator {n : ℕ} (g : (Fin n → ℝ) → EReal) (y : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {u | IsMinOn (fun v => g v + ((1 : EReal) / 2) * (∑ i : Fin n, (v i - y i) ^ 2)) Set.univ u}

theorem proximalOperator_comp_affine
    {n : ℕ} (g : (Fin n → ℝ) → EReal) (lam : ℝ) (a x : Fin n → ℝ) (hlam : lam ≠ 0) :
    proximalOperator (fun z => g (fun i => lam * z i + a i)) x =
      {u | (fun i => lam * u i + a i) ∈
        proximalOperator (fun z => (lam ^ 2 : EReal) * g z) (fun i => lam * x i + a i)} := by
  sorry

end «CAM-Bench-772»
