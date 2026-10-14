import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-253»

open scoped BigOperators

def supportFunction (C : Set (Fin n → ℝ)) (y : Fin n → ℝ) : EReal :=
  sSup ((fun c : Fin n → ℝ => (∑ i, c i * y i : ℝ)) '' C)

theorem mem_permutahedron_iff_partial_sums_le
    (n : ℕ) (a x : Fin n → ℝ)
    (C : Set (Fin n → ℝ))
    (hC :
      C = {c | ∃ e : Equiv.Perm (Fin n), c = fun i => a (e i)}) :
    ((∀ y : Fin n → ℝ, ((↑(∑ i, x i * y i) : EReal) ≤ supportFunction C y)) ↔
      let sx := (List.ofFn x).mergeSort (· ≥ ·)
      let sa := (List.ofFn a).mergeSort (· ≥ ·)
      (∀ k : Fin (n - 1), 1 ≤ k.1 + 1 →
        (∑ i : Fin (k.1 + 1), sx[i.1]!) ≤
          ∑ i : Fin (k.1 + 1), sa[i.1]!) ∧
      ((∑ i : Fin n, sx[i.1]!) = ∑ i : Fin n, sa[i.1]!)) := by
  sorry

end «CAM-Bench-253»
