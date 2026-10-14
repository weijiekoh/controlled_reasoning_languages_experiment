import Mathlib
def cnt (k n : ℕ) : ℕ := ((List.finRange n).permutations.filter (fun p =>
  decide (∀ i : Fin n, |((p.getD i.val 0 : ℕ) : ℤ) - i| ≤ k))).length
#eval (List.range 8).map (fun n => (n+1, cnt 1 (n+1) % 2))
