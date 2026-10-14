  have hg : Tendsto (fun n:ℕ => 8 / Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
    have hs : Tendsto (fun n:ℕ => Real.sqrt (n:ℝ)) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨⌈max b 0 ^ 2⌉₊, fun n hn => ?_⟩
      have hn' : max b 0 ^ 2 ≤ (n:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
      have hs0 := Real.sqrt_nonneg (n:ℝ)
      have hsq := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
      nlinarith [le_max_left b 0, le_max_right b 0]
    have := (tendsto_const_nhds (x := (8:ℝ))).div_atTop hs
    simpa using this
  apply Iff.intro
  · intro _
    trivial
  · intro _
    refine ⟨0, ?_⟩
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := by linarith
      have h1 : (n:ℝ) ≤ exp (a n) := by linarith [hlow n, Real.exp_one_gt_d9]
      have := Real.log_le_log hnpos h1
      rw [Real.log_exp] at this
      show (0:ℝ) ≤ a n - Real.log n
      linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0:ℝ) < n := by linarith
      have hsn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnpos
      have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ n by positivity)
      have ht2 := Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)
      have ht0 := Real.sqrt_nonneg ((n:ℝ)+1)
      have hts : Real.sqrt ((n:ℝ)+1) ≤ 2 * Real.sqrt (n:ℝ) := by
        nlinarith
      have hA := Real.log_le_log (Real.exp_pos _) (hup n)
      rw [Real.log_exp] at hA
      have hpos2 : (0:ℝ) < n + 4 * Real.sqrt ((n:ℝ)+1) := by positivity
      have hB : Real.log ((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) - Real.log n
          = Real.log (((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) / n) := by
        rw [Real.log_div hpos2.ne' hnpos.ne']
      have hC := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) / n by positivity)
      have hD : (((n:ℝ) + 4 * Real.sqrt ((n:ℝ)+1)) / n) - 1 = 4 * Real.sqrt ((n:ℝ)+1) / n := by
        field_simp
        ring
      have hE : 4 * Real.sqrt ((n:ℝ)+1) / n ≤ 8 / Real.sqrt (n:ℝ) := by
        rw [div_le_div_iff₀ hnpos hsn]
        nlinarith
      show a n - Real.log n ≤ 8 / Real.sqrt (n:ℝ)
      linarith
