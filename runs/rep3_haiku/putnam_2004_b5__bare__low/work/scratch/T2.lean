
lemma sum_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (N : ℕ) :
    Real.log 2 - 1 - (1 - x) ≤ ∑ n ∈ Finset.range N, x^n * (Real.log (1 + x^(n+1)) - Real.log (1 + x^n)) ∧
    ∑ n ∈ Finset.range N, x^n * (Real.log (1 + x^(n+1)) - Real.log (1 + x^n)) ≤ Real.log 2 - 1 + x^N := by
  set G : ℕ → ℝ := fun n => x^n - Real.log (1 + x^n) with hG
  set e : ℕ → ℝ := fun n => x^n * (Real.log (1 + x^(n+1)) - Real.log (1 + x^n)) - (G (n+1) - G n) with he
  have hT : ∀ n, x^n * (Real.log (1 + x^(n+1)) - Real.log (1 + x^n)) = (G (n+1) - G n) + e n := by
    intro n; simp only [he]; ring
  have hsplit : ∑ n ∈ Finset.range N, x^n * (Real.log (1 + x^(n+1)) - Real.log (1 + x^n))
      = (G N - G 0) + ∑ n ∈ Finset.range N, e n := by
    rw [Finset.sum_congr rfl (fun n _ => hT n), Finset.sum_add_distrib, Finset.sum_range_sub]
  have heb : ∀ n ∈ Finset.range N, -((1 - x) * (x^n - x^(n+1))) ≤ e n ∧ e n ≤ 0 := by
    intro n _
    have ha : 0 < x^n := pow_pos hx0 n
    have ha1 : x^n ≤ 1 := pow_le_one₀ hx0.le hx1.le
    have := term_bound x (x^n) hx0 hx1 ha ha1
    rw [← pow_succ] at this
    simp only [he, hG]
    constructor <;> nlinarith [this.1, this.2]
  have hsumU : ∑ n ∈ Finset.range N, e n ≤ 0 :=
    Finset.sum_nonpos (fun n hn => (heb n hn).2)
  have hsumL : -(1 - x) ≤ ∑ n ∈ Finset.range N, e n := by
    have h1 : ∑ n ∈ Finset.range N, -((1 - x) * (x^n - x^(n+1))) ≤ ∑ n ∈ Finset.range N, e n :=
      Finset.sum_le_sum (fun n hn => (heb n hn).1)
    have hs : ∑ n ∈ Finset.range N, (x^n - x^(n+1)) = 1 - x^N := by
      rw [Finset.sum_range_sub']; simp
    have h2 : ∑ n ∈ Finset.range N, -((1 - x) * (x^n - x^(n+1))) = -(1-x) * (1 - x^N) := by
      rw [← hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _; ring
    have h3 : 0 ≤ x^N := pow_nonneg hx0.le N
    nlinarith
  have hG0 : G 0 = 1 - Real.log 2 := by
    simp only [hG, pow_zero]; norm_num
  have hGN : G N = x^N - Real.log (1 + x^N) := rfl
  have hlog0 : 0 ≤ Real.log (1 + x^N) := Real.log_nonneg (by linarith [pow_nonneg hx0.le N])
  have hlog1 : Real.log (1 + x^N) ≤ x^N := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + x^N by linarith [pow_nonneg hx0.le N])
    linarith
  rw [hsplit, hG0, hGN]
  constructor <;> linarith
