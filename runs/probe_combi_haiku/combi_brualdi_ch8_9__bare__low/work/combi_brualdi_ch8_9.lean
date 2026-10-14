import Mathlib

/--
Prove that the following formula holds for the $k$ th-order differences of a sequence $h_{0}, h_{1}, \ldots, h_{n}, \ldots$ : \Delta^{k} h_{n}=\sum_{j=0}^{k}(-1)^{k-j}\binom{k}{j} h_{n+j}
-/
theorem brualdi_ch8_9 (h : ℕ → ℤ) (k n : ℕ): (fwdDiff 1)^[k] h n = ∑ j ∈ Finset.range (k + 1),
    (-1 : ℤ) ^ (k - j) * Nat.choose k j * h (n + j) := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl ?_
  intro j _
  simp only [smul_eq_mul, nsmul_eq_mul, one_smul, mul_comm]
  push_cast
  ring_nf
