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
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ t, g t = Real.log (1 + t) := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ t, F t = (1 + t) * Real.log (1 + t) - t := ⟨_, fun _ => rfl⟩
  have hFd : ∀ t : ℝ, -1 < t → HasDerivAt F (g t) t := by
    intro t ht
    have hne : (1:ℝ) + t ≠ 0 := ne_of_gt (by linarith)
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id' t).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t :=
      h1.log hne
    have h3 := ((h1.mul h2).sub (hasDerivAt_id' t))
    have hFe : F = fun s : ℝ => (1 + s) * Real.log (1 + s) - s := funext hF
    rw [hFe]
    exact h3.congr_deriv (by rw [hg]; field_simp; ring)
  have hMVT : ∀ u v : ℝ, 0 < v → v < u → u ≤ 1 →
      (u - v) * g v ≤ F u - F v ∧ F u - F v ≤ (u - v) * g u := by
    intro u v hv hvu hu1
    have hcont : ContinuousOn F (Set.Icc v u) := fun s hs =>
      (hFd s (by linarith [hs.1])).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F g hvu hcont
      (fun s hs => hFd s (by linarith [hs.1]))
    have hgv : g v ≤ g c := by
      rw [hg, hg]; exact Real.log_le_log (by linarith) (by linarith [hc.1])
    have hgu : g c ≤ g u := by
      rw [hg, hg]; exact Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
    have hpos : 0 < u - v := by linarith
    have hE : F u - F v = g c * (u - v) := by
      rw [hceq]; field_simp
    constructor <;> nlinarith
  have hconc : ∀ u x : ℝ, 0 ≤ u → 0 ≤ x → x ≤ 1 → x * g u ≤ g (x * u) := by
    intro u x hu hx0 hx1
    rw [hg, hg]
    have hb : (1 + u) ^ x ≤ 1 + x * u :=
      rpow_one_add_le_one_add_mul_self (s := u) (p := x) (by linarith) hx0 hx1
    have hl : Real.log ((1 + u) ^ x) = x * Real.log (1 + u) := Real.log_rpow (by linarith) x
    rw [← hl]
    exact Real.log_le_log (Real.rpow_pos_of_pos (by linarith) x) hb
  have hg0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ g t ∧ g t ≤ t := by
    intro t ht
    rw [hg]
    constructor
    · exact Real.log_nonneg (by linarith)
    · have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + t by linarith)
      linarith
  have hF0 : F 0 = 0 := by rw [hF]; simp
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      Real.exp (-g 1 + (F x - F 0) / x) ≤ xprod x ∧
        xprod x ≤ Real.exp (-g 1 + (F x - F 0) / x ^ 2 + 0) := by
    intro x hx0 hx1
    have hsum : ∀ n : ℕ,
        x * (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1))) ≥ F x - F (x ^ (n + 1)) ∧
        x ^ 2 * (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1))) ≤ F x - F (x ^ (n + 1)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ]
        obtain ⟨ih1, ih2⟩ := ih
        have hu0 : 0 < x ^ (n + 1) := pow_pos hx0 _
        have hu1 : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx0.le hx1.le
        have hv : x ^ (n + 1 + 1) = x * x ^ (n + 1) := by ring
        rw [hv]
        have hvu : x * x ^ (n + 1) < x ^ (n + 1) := by nlinarith
        obtain ⟨hA1, hA2⟩ := hMVT (x ^ (n + 1)) (x * x ^ (n + 1)) (by positivity) hvu hu1
        have hC := hconc (x ^ (n + 1)) x hu0.le hx0.le hx1.le
        have hpos' : 0 ≤ x ^ (n + 1) - x * x ^ (n + 1) := by linarith
        have e1 : x * ((1 - x) * x ^ n * g (x ^ (n + 1)))
            = (x ^ (n + 1) - x * x ^ (n + 1)) * g (x ^ (n + 1)) := by ring
        have e2 : x ^ 2 * ((1 - x) * x ^ n * g (x ^ (n + 1)))
            = (x ^ (n + 1) - x * x ^ (n + 1)) * (x * g (x ^ (n + 1))) := by ring
        have e3 := mul_le_mul_of_nonneg_left hC hpos'
        constructor
        · have : x * (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1))
              + (1 - x) * x ^ n * g (x ^ (n + 1)))
              = x * (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1)))
                + x * ((1 - x) * x ^ n * g (x ^ (n + 1))) := by ring
          rw [this, e1]
          linarith
        · have : x ^ 2 * (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1))
              + (1 - x) * x ^ n * g (x ^ (n + 1)))
              = x ^ 2 * (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1)))
                + x ^ 2 * ((1 - x) * x ^ n * g (x ^ (n + 1))) := by ring
          rw [this, e2]
          linarith
    obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ, ∀ N, D N =
        ∑ k ∈ Finset.range N, x ^ k * (g (x ^ (k + 1)) - g (x ^ k)) := ⟨_, fun _ => rfl⟩
    have hSBP : ∀ n : ℕ, D (n + 1) = -g 1
        + (∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1)))
        + x ^ n * g (x ^ (n + 1)) := by
      intro n
      induction n with
      | zero => simp [hD]; ring
      | succ n ih =>
        have hstep : D (n + 1 + 1) = D (n + 1)
            + x ^ (n + 1) * (g (x ^ (n + 1 + 1)) - g (x ^ (n + 1))) := by
          rw [hD, hD, Finset.sum_range_succ]
        rw [hstep, ih, Finset.sum_range_succ]
        simp only [pow_succ]
        ring
    have hprod : ∀ N : ℕ, ∏ k ∈ Finset.range N, ((1 + x ^ (k + 1)) / (1 + x ^ k)) ^ (x ^ k)
        = Real.exp (D N) := by
      intro N
      rw [hD, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro k _
      have ha : 0 < 1 + x ^ (k + 1) := by have := pow_pos hx0 (k + 1); linarith
      have hb : 0 < 1 + x ^ k := by have := pow_pos hx0 k; linarith
      rw [Real.rpow_def_of_pos (div_pos ha hb), hg, hg, Real.log_div ha.ne' hb.ne']
      congr 1
      ring
    have htend : Filter.Tendsto (fun N => Real.exp (D N)) Filter.atTop (nhds (xprod x)) :=
      Filter.Tendsto.congr (fun N => hprod N) (hxprod x ⟨hx0, hx1⟩)
    have htend' : Filter.Tendsto (fun n => Real.exp (D (n + 1))) Filter.atTop (nhds (xprod x)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr htend
    have hpow : Filter.Tendsto (fun n : ℕ => x ^ (n + 1)) Filter.atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1)
    have hFc : Filter.Tendsto (fun n : ℕ => F (x ^ (n + 1))) Filter.atTop (nhds (F 0)) := by
      have hc0 : ContinuousAt F 0 := (hFd 0 (by norm_num)).continuousAt
      exact hc0.tendsto.comp hpow
    have hpowN := tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hEb : Filter.Tendsto (fun n : ℕ => x ^ n * g (x ^ (n + 1))) Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun n => ?_) (fun n => ?_) hpowN
      · exact mul_nonneg (pow_nonneg hx0.le n) (hg0 _ (pow_nonneg hx0.le _)).1
      · have h1 := (hg0 (x ^ (n + 1)) (pow_nonneg hx0.le _)).2
        have h2 : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx0.le hx1.le
        exact mul_le_of_le_one_right (pow_nonneg hx0.le n) (by linarith)
    have hLo : Filter.Tendsto (fun n : ℕ => Real.exp (-g 1 + (F x - F (x ^ (n + 1))) / x))
        Filter.atTop (nhds (Real.exp (-g 1 + (F x - F 0) / x))) :=
      (Real.continuous_exp.tendsto _).comp
        (tendsto_const_nhds.add ((tendsto_const_nhds.sub hFc).div_const x))
    have hHi : Filter.Tendsto
        (fun n : ℕ => Real.exp (-g 1 + (F x - F (x ^ (n + 1))) / x ^ 2 + x ^ n))
        Filter.atTop (nhds (Real.exp (-g 1 + (F x - F 0) / x ^ 2 + 0))) :=
      (Real.continuous_exp.tendsto _).comp
        ((tendsto_const_nhds.add ((tendsto_const_nhds.sub hFc).div_const _)).add hpowN)
    constructor
    · refine le_of_tendsto_of_tendsto hLo htend' (Filter.Eventually.of_forall fun n => ?_)
      have hS := (hsum n).1
      have hE : 0 ≤ x ^ n * g (x ^ (n + 1)) :=
        mul_nonneg (pow_nonneg hx0.le n) (hg0 _ (pow_nonneg hx0.le _)).1
      have hdiv : (F x - F (x ^ (n + 1))) / x ≤ ∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1)) := by
        rw [div_le_iff₀ hx0]
        linarith
      dsimp only
      rw [hSBP n]
      apply Real.exp_le_exp.mpr
      linarith
    · refine le_of_tendsto_of_tendsto htend' hHi (Filter.Eventually.of_forall fun n => ?_)
      have hS := (hsum n).2
      have hEn : x ^ n * g (x ^ (n + 1)) ≤ x ^ n := by
        have h1 := (hg0 (x ^ (n + 1)) (pow_nonneg hx0.le _)).2
        have h2 : x ^ (n + 1) ≤ 1 := pow_le_one₀ hx0.le hx1.le
        exact mul_le_of_le_one_right (pow_nonneg hx0.le n) (by linarith)
      have hdiv : ∑ k ∈ Finset.range n, (1 - x) * x ^ k * g (x ^ (k + 1)) ≤ (F x - F (x ^ (n + 1))) / x ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      dsimp only
      rw [hSBP n]
      apply Real.exp_le_exp.mpr
      linarith
  have hFc1 : ContinuousAt F 1 := (hFd 1 (by norm_num)).continuousAt
  have hcL : ContinuousAt (fun x => Real.exp (-g 1 + (F x - F 0) / x)) 1 := by
    apply ContinuousAt.comp (g := Real.exp) (Real.continuous_exp.continuousAt)
    apply ContinuousAt.add continuousAt_const
    exact ContinuousAt.div (hFc1.sub continuousAt_const) continuousAt_id (by norm_num)
  have hcU : ContinuousAt (fun x => Real.exp (-g 1 + (F x - F 0) / x ^ 2 + 0)) 1 := by
    apply ContinuousAt.comp (g := Real.exp) (Real.continuous_exp.continuousAt)
    apply ContinuousAt.add _ continuousAt_const
    apply ContinuousAt.add continuousAt_const
    exact ContinuousAt.div (hFc1.sub continuousAt_const) (continuousAt_id.pow 2) (by norm_num)
  have hL := hcL.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  have hU := hcU.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  have eL : Real.exp (-g 1 + (F 1 - F 0) / 1) = Real.exp (-g 1 + (F 1 - F 0) / 1 ^ 2 + 0) := by
    norm_num
  rw [eL] at hL
  have hev : ∀ᶠ x in nhdsWithin (1:ℝ) (Set.Iio 1), 0 < x ∧ x < 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    exact hx
  have hfin := tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU
    (hev.mono fun x hx => (key x hx.1 hx.2).1)
    (hev.mono fun x hx => (key x hx.1 hx.2).2)
  have h1 : g 1 = Real.log 2 := by rw [hg]; norm_num
  have h2 : F 1 = 2 * Real.log 2 - 1 := by rw [hF]; norm_num
  have hval : Real.exp (-g 1 + (F 1 - F 0) / 1 ^ 2 + 0) = putnam_2004_b5_solution := by
    rw [h1, h2, hF0]
    have : -Real.log 2 + (2 * Real.log 2 - 1 - 0) / 1 ^ 2 + 0 = Real.log 2 - 1 := by ring
    rw [this, Real.exp_sub, Real.exp_log two_pos]
  rw [hval] at hfin
  exact hfin
