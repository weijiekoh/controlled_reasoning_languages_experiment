
theorem putnam_2004_b5
    (xprod : ℝ → ℝ)
    (hxprod : ∀ x ∈ Set.Ioo 0 1,
      Tendsto (fun N ↦ ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
      atTop (𝓝 (xprod x))) :
    Tendsto xprod (𝓝[<] 1) (𝓝 putnam_2004_b5_solution) := by
  have hc : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      Real.exp (Real.log 2 - 1 - (1 - x)) ≤ xprod x ∧ xprod x ≤ Real.exp (Real.log 2 - 1) := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hP : ∀ N : ℕ, ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (∑ n ∈ Finset.range N, x^n * (Real.log (1 + x^(n+1)) - Real.log (1 + x^n))) := by
      intro N
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro n _
      have hp : 0 < 1 + x^n := by linarith [pow_pos hx0 n]
      have hq : 0 < 1 + x^(n+1) := by linarith [pow_pos hx0 (n+1)]
      rw [Real.rpow_def_of_pos (div_pos hq hp), Real.log_div hq.ne' hp.ne']
      congr 1
      ring
    have hlim := Tendsto.congr hP (hxprod x ⟨hx0, hx1⟩)
    constructor
    · apply ge_of_tendsto hlim
      exact Filter.Eventually.of_forall (fun N => Real.exp_le_exp.mpr (sum_bound x hx0 hx1 N).1)
    · have hg : Tendsto (fun N : ℕ => Real.exp (Real.log 2 - 1 + x^N)) atTop
          (𝓝 (Real.exp (Real.log 2 - 1))) := by
        have h0 : Tendsto (fun N : ℕ => x^N) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
        have h1 : Tendsto (fun N : ℕ => Real.exp (Real.log 2 - 1 + x^N)) atTop
            (𝓝 (Real.exp (Real.log 2 - 1 + 0))) :=
          (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.add h0)
        rwa [add_zero] at h1
      apply le_of_tendsto_of_tendsto hlim hg
      exact Filter.Eventually.of_forall (fun N => Real.exp_le_exp.mpr (sum_bound x hx0 hx1 N).2)
  have hsol : putnam_2004_b5_solution = Real.exp (Real.log 2 - 1) := by
    rw [show putnam_2004_b5_solution = 2 / Real.exp 1 from rfl]
    rw [Real.exp_sub, Real.exp_log two_pos]
  rw [hsol]
  have hcont : Continuous (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) := by fun_prop
  have hlow : Tendsto (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) (𝓝[<] 1)
      (𝓝 (Real.exp (Real.log 2 - 1))) := by
    convert (hcont.tendsto 1).mono_left nhdsWithin_le_nhds using 2
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    exact (hc x hx).1
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    exact (hc x hx).2
