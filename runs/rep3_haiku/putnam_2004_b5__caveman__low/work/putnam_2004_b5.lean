import Mathlib

open Nat Topology Filter

noncomputable abbrev putnam_2004_b5_solution : ℝ := 2 / Real.exp 1
/--
Evaluate $\lim_{x \to 1^-} \prod_{n=0}^\infty \left(\frac{1+x^{n+1}}{1+x^n}\right)^{x^n}$.
-/
theorem putnam_2004_b5
    (xprod : ℝ → ℝ)
    (hxprod : ∀ x ∈ Set.Ioo 0 1,
      Tendsto (fun N ↦ ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
      atTop (𝓝 (xprod x))) :
    Tendsto xprod (𝓝[<] 1) (𝓝 putnam_2004_b5_solution) := by
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ t, F t = (1 + t) * Real.log (1 + t) - t :=
    ⟨fun t => (1 + t) * Real.log (1 + t) - t, fun t => rfl⟩
  have hFd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (Real.log (1 + t)) t := by
    intro t ht
    have hFeq : F = fun t => (1 + t) * Real.log (1 + t) - t := funext hF
    rw [hFeq]
    have hpos : (1 + t) ≠ 0 := (by linarith : (0:ℝ) < 1 + t).ne'
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
      simpa using (hasDerivAt_id' t).const_add (1:ℝ)
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + t)) t := h1.log hpos
    have h3 := (h1.mul h2).sub (hasDerivAt_id' t)
    have h4 : (1 + t) * (1 / (1 + t)) = 1 := by field_simp
    refine h3.congr_deriv ?_
    linarith
  have hmvt : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      Real.log (1 + a) * (b - a) ≤ F b - F a ∧ F b - F a ≤ Real.log (1 + b) * (b - a) := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h | h
    · subst h; simp
    have hcont : ContinuousOn F (Set.Icc a b) :=
      fun t ht => (hFd t (le_trans ha ht.1)).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F (fun t => Real.log (1 + t)) h hcont
      (fun t ht => hFd t (le_trans ha ht.1.le))
    have hceq' : Real.log (1 + c) = (F b - F a) / (b - a) := hceq
    have hba : 0 < b - a := by linarith
    have hFe : F b - F a = Real.log (1 + c) * (b - a) := by
      rw [hceq']; field_simp
    have h1 : Real.log (1 + a) ≤ Real.log (1 + c) :=
      Real.log_le_log (by linarith) (by linarith [hc.1])
    have h2 : Real.log (1 + c) ≤ Real.log (1 + b) :=
      Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
    rw [hFe]
    exact ⟨mul_le_mul_of_nonneg_right h1 hba.le, mul_le_mul_of_nonneg_right h2 hba.le⟩
  have hF00 : F 0 = 0 := by rw [hF]; simp
  have hFnn : ∀ t, 0 ≤ t → 0 ≤ F t ∧ F t ≤ t * Real.log (1 + t) := by
    intro t ht
    have := hmvt 0 t le_rfl ht
    simp only [hF00, add_zero, Real.log_one, zero_mul, sub_zero] at this
    exact ⟨this.1, by linarith [this.2, mul_comm t (Real.log (1 + t))]⟩
  have hlog_nonneg : ∀ t, 0 ≤ t → 0 ≤ Real.log (1 + t) :=
    fun t ht => Real.log_nonneg (by linarith)
  have hlog_mono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.log (1 + a) ≤ Real.log (1 + b) :=
    fun a b ha hab => Real.log_le_log (by linarith) (by linarith)
  have key : ∀ x : ℝ, 0 < x → x < 1 → ∃ L : ℝ, xprod x = Real.exp L ∧
      (F x - x * Real.log 2) / x ≤ L ∧ L ≤ (F x - x ^ 2 * Real.log 2) / x := by
    intro x hx0 hx1
    obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ N, T N =
        ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)) :=
      ⟨_, fun N => rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ N, S N =
        ∑ k ∈ Finset.range N, Real.log (1 + x ^ (k + 1)) * (x ^ (k + 1) - x ^ (k + 2)) :=
      ⟨_, fun N => rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ n, g n = x ^ n * Real.log (1 + x ^ n) :=
      ⟨_, fun n => rfl⟩
    have hTs : ∀ N, T (N + 1) = T N + x ^ N * (Real.log (1 + x ^ (N + 1)) - Real.log (1 + x ^ N)) := by
      intro N; rw [hT, hT, Finset.sum_range_succ]
    have hSs : ∀ N, S (N + 1) = S N + Real.log (1 + x ^ (N + 1)) * (x ^ (N + 1) - x ^ (N + 2)) := by
      intro N; rw [hS, hS, Finset.sum_range_succ]
    have hI : ∀ N, x * T (N + 1) = S N + g (N + 1) - x * Real.log 2 := by
      intro N
      induction N with
      | zero =>
        simp [hTs 0, hT, hS, hg]
        ring_nf
      | succ n ih =>
        rw [hTs (n + 1), hSs n, hg (n + 1 + 1)]
        rw [hg (n + 1)] at ih
        linear_combination ih
    have hSb : ∀ N, F x - F (x ^ (N + 1)) ≤ S N ∧
        S N ≤ F x - F (x ^ (N + 1)) + x * (1 - x) * (Real.log (1 + x) - Real.log (1 + x ^ (N + 1))) := by
      intro N
      induction N with
      | zero => simp [hS]
      | succ n ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have ha0 : 0 ≤ x ^ (n + 1 + 1) := pow_nonneg hx0.le _
        have hab : x ^ (n + 1 + 1) ≤ x ^ (n + 1) :=
          pow_le_pow_of_le_one hx0.le hx1.le (by omega)
        have hd := hmvt (x ^ (n + 1 + 1)) (x ^ (n + 1)) ha0 hab
        have hx1' : x ^ (n + 1) ≤ x := by
          have := pow_le_pow_of_le_one hx0.le hx1.le (show 1 ≤ n + 1 by omega)
          simpa using this
        have hdiff : x ^ (n + 1) - x ^ (n + 1 + 1) ≤ x * (1 - x) := by
          have e : x ^ (n + 1 + 1) = x ^ (n + 1) * x := pow_succ _ _
          have := mul_le_mul_of_nonneg_right hx1' (by linarith : (0:ℝ) ≤ 1 - x)
          rw [e]; nlinarith
        have hphi : 0 ≤ Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ (n + 1 + 1)) := by
          linarith [hlog_mono _ _ ha0 hab]
        have hm := mul_le_mul_of_nonneg_left hdiff hphi
        have hterm : Real.log (1 + x ^ (n + 1)) * (x ^ (n + 1) - x ^ (n + 1 + 1)) ≤
            (F (x ^ (n + 1)) - F (x ^ (n + 1 + 1))) +
              x * (1 - x) * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ (n + 1 + 1))) := by
          nlinarith [hd.1, hm]
        rw [hSs n]
        constructor
        · linarith [hd.2]
        · linarith [hterm]
    have hlow : ∀ N, (F x - x * Real.log 2) / x ≤ T (N + 1) := by
      intro N
      have h1 := hI N
      have h2 := (hSb N).1
      have h3 := (hFnn (x ^ (N + 1)) (pow_nonneg hx0.le _)).2
      rw [div_le_iff₀ hx0]
      rw [hg] at h1
      nlinarith
    have hup : ∀ N, T (N + 1) ≤ (F x - x ^ 2 * Real.log 2 + g (N + 1)) / x := by
      intro N
      have h1 := hI N
      have h2 := (hSb N).2
      have h3 := (hFnn (x ^ (N + 1)) (pow_nonneg hx0.le _)).1
      have h5 : Real.log (1 + x) ≤ Real.log 2 := Real.log_le_log (by linarith) (by linarith)
      have h6 : 0 ≤ x * (1 - x) := mul_nonneg hx0.le (by linarith)
      have h7 : x * (1 - x) * (Real.log (1 + x) - Real.log (1 + x ^ (N + 1))) ≤
          x * (1 - x) * Real.log 2 := by
        apply mul_le_mul_of_nonneg_left _ h6
        linarith [hlog_nonneg (x ^ (N + 1)) (pow_nonneg hx0.le _)]
      rw [le_div_iff₀ hx0]
      nlinarith
    have hg0 : Filter.Tendsto g Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
      have hc : ContinuousAt (fun t : ℝ => Real.log (1 + t)) 0 :=
        ContinuousAt.log (by fun_prop) (by norm_num)
      have h2 : Filter.Tendsto (fun n : ℕ => Real.log (1 + x ^ n)) Filter.atTop (nhds 0) := by
        have h := hc.tendsto.comp h1
        have e : Real.log (1 + 0) = 0 := by simp
        rw [e] at h
        exact h
      have : Filter.Tendsto (fun n : ℕ => x ^ n * Real.log (1 + x ^ n)) Filter.atTop (nhds 0) := by
        simpa using h1.mul h2
      have e : g = fun n => x ^ n * Real.log (1 + x ^ n) := funext hg
      rw [e]
      exact this
    have hgshift : Filter.Tendsto (fun N => g (N + 1)) Filter.atTop (nhds 0) :=
      hg0.comp (Filter.tendsto_add_atTop_nat 1)
    have hanti : Antitone T := by
      apply antitone_nat_of_succ_le
      intro n
      rw [hTs n]
      have h0 : 0 ≤ x ^ n := pow_nonneg hx0.le _
      have hle : x ^ (n + 1) ≤ x ^ n := pow_le_pow_of_le_one hx0.le hx1.le (by omega)
      have hl := hlog_mono _ _ (pow_nonneg hx0.le (n + 1)) hle
      nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ Real.log (1 + x ^ n) - Real.log (1 + x ^ (n + 1)))]
    have hbdd : BddBelow (Set.range T) := by
      refine ⟨min ((F x - x * Real.log 2) / x) 0, ?_⟩
      rintro _ ⟨N, rfl⟩
      cases N with
      | zero => rw [hT, Finset.sum_range_zero]; exact min_le_right _ _
      | succ n => exact le_trans (min_le_left _ _) (hlow n)
    have hTlim := tendsto_atTop_ciInf hanti hbdd
    have hL1 := hTlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hlo : (F x - x * Real.log 2) / x ≤ ⨅ i, T i :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds hL1 hlow
    have hhi : (⨅ i, T i) ≤ (F x - x ^ 2 * Real.log 2) / x := by
      have hT2 := (hgshift.const_add (F x - x ^ 2 * Real.log 2)).div_const x
      rw [add_zero] at hT2
      exact le_of_tendsto_of_tendsto' hL1 hT2 hup
    have hprod : ∀ N, ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (T N) := by
      intro N
      rw [hT, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro n _
      have hp1 : 0 < 1 + x ^ (n + 1) := by linarith [pow_nonneg hx0.le (n + 1)]
      have hp2 : 0 < 1 + x ^ n := by linarith [pow_nonneg hx0.le n]
      rw [Real.rpow_def_of_pos (div_pos hp1 hp2), Real.log_div hp1.ne' hp2.ne']
      congr 1
      ring
    have hlim : Filter.Tendsto (fun N => ∏ n ∈ Finset.range N,
        ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)) Filter.atTop
        (nhds (Real.exp (⨅ i, T i))) :=
      ((Real.continuous_exp.tendsto _).comp hTlim).congr (fun N => (hprod N).symm)
    exact ⟨⨅ i, T i, tendsto_nhds_unique (hxprod x ⟨hx0, hx1⟩) hlim, hlo, hhi⟩
  have hev : ∀ᶠ x in 𝓝[<] (1:ℝ), x ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have hlo_c : Filter.Tendsto (fun x : ℝ => ((1 + x) * Real.log (1 + x) - x - x * Real.log 2) / x)
      (nhds 1) (nhds (Real.log 2 - 1)) := by
    have hc : ContinuousAt (fun x : ℝ => ((1 + x) * Real.log (1 + x) - x - x * Real.log 2) / x) 1 := by
      apply ContinuousAt.div
      · fun_prop (disch := norm_num)
      · exact continuousAt_id
      · norm_num
    have hv : ((fun x : ℝ => ((1 + x) * Real.log (1 + x) - x - x * Real.log 2) / x) 1)
        = Real.log 2 - 1 := by
      norm_num <;> ring
    rw [← hv]; exact hc.tendsto
  have hhi_c : Filter.Tendsto (fun x : ℝ => ((1 + x) * Real.log (1 + x) - x - x ^ 2 * Real.log 2) / x)
      (nhds 1) (nhds (Real.log 2 - 1)) := by
    have hc : ContinuousAt (fun x : ℝ => ((1 + x) * Real.log (1 + x) - x - x ^ 2 * Real.log 2) / x) 1 := by
      apply ContinuousAt.div
      · fun_prop (disch := norm_num)
      · exact continuousAt_id
      · norm_num
    have hv : ((fun x : ℝ => ((1 + x) * Real.log (1 + x) - x - x ^ 2 * Real.log 2) / x) 1)
        = Real.log 2 - 1 := by
      norm_num <;> ring
    rw [← hv]; exact hc.tendsto
  have hexp : Real.exp (Real.log 2 - 1) = 2 / Real.exp 1 := by
    rw [Real.exp_sub, Real.exp_log two_pos]
  show Filter.Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  rw [← hexp]
  have hL : Filter.Tendsto (fun x : ℝ => Real.exp (((1 + x) * Real.log (1 + x) - x - x * Real.log 2) / x))
      (𝓝[<] 1) (nhds (Real.exp (Real.log 2 - 1))) :=
    ((Real.continuous_exp.tendsto _).comp hlo_c).mono_left nhdsWithin_le_nhds
  have hH : Filter.Tendsto (fun x : ℝ => Real.exp (((1 + x) * Real.log (1 + x) - x - x ^ 2 * Real.log 2) / x))
      (𝓝[<] 1) (nhds (Real.exp (Real.log 2 - 1))) :=
    ((Real.continuous_exp.tendsto _).comp hhi_c).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hH ?_ ?_
  · filter_upwards [hev] with x hx
    obtain ⟨L, hLe, h1, _⟩ := key x hx.1 hx.2
    simp only [hF] at h1
    rw [hLe]
    exact Real.exp_le_exp.mpr h1
  · filter_upwards [hev] with x hx
    obtain ⟨L, hLe, _, h2⟩ := key x hx.1 hx.2
    simp only [hF] at h2
    rw [hLe]
    exact Real.exp_le_exp.mpr h2
