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
    Tendsto xprod (𝓝[<] 1) (𝓝 putnam_2004_b5_solution) :=
  by
  set f : ℝ → ℝ := fun t => Real.log (1 + t) with hf
  set F : ℝ → ℝ := fun t => (1 + t) * Real.log (1 + t) - t with hF
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt F (f t) t := by
    intro t ht
    have h1 : (1 + t) ≠ 0 := by positivity
    have h3 : HasDerivAt (fun t : ℝ => (1 + t) * Real.log (1 + t) - t) (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1) t := by
      have hh : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id' t).const_add 1
      have := (hh.mul (hh.log h1)).sub (hasDerivAt_id' t)
      exact this
    have e : 1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1 = f t := by
      field_simp; simp [hf]
    rw [e] at h3
    exact h3
  have fmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a ≤ f b := by
    intro a b ha hab
    exact Real.log_le_log (by linarith) (by linarith)
  have hA : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f a * (b - a) ≤ F b - F a ∧ F b - F a ≤ f b * (b - a) := by
    intro a b ha hab
    have hint : ∫ t in a..b, f t = F b - F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hd t (by rw [Set.uIcc_of_le hab] at ht; linarith [ht.1]))
        (ContinuousOn.intervalIntegrable (by
          apply ContinuousOn.log (by fun_prop)
          intro t ht
          rw [Set.uIcc_of_le hab] at ht
          linarith [ht.1]))
    have hc : ContinuousOn f (Set.Icc a b) := by
      apply ContinuousOn.log (by fun_prop)
      intro t ht; linarith [ht.1]
    have hi : IntervalIntegrable f MeasureTheory.volume a b :=
      (hc.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable
    constructor
    · rw [← hint]
      have := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := f a)) hi
        (fun t ht => fmono a t ha ht.1)
      simpa [mul_comm] using this
    · rw [← hint]
      have := intervalIntegral.integral_mono_on hab hi (intervalIntegrable_const (c := f b))
        (fun t ht => fmono t b (by linarith [ht.1]) ht.2)
      simpa [mul_comm] using this
  have F0 : F 0 = 0 := by simp [hF]
  have f0 : f 0 = 0 := by simp [hf]
  have F1 : F 1 = 2 * Real.log 2 - 1 := by
    simp only [hF]; norm_num
  have f1 : f 1 = Real.log 2 := by simp [hf]; norm_num
  have fc : ContinuousAt f 0 := by
    simp only [hf]; exact ContinuousAt.log (by fun_prop) (by norm_num)
  have Fc : ContinuousAt F 0 := (hd 0 le_rfl).continuousAt
  have key : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      Real.exp (-f 1 + F 1 - (1 - x) * f 1) ≤ xprod x ∧ xprod x ≤ Real.exp (-f 1 + F 1) := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hpow : ∀ n : ℕ, 0 < x ^ n := fun n => pow_pos hx0 n
    have hform : ∀ N : ℕ, ∑ n ∈ Finset.range (N+1), x^n * (f (x^(n+1)) - f (x^n))
        = -f 1 + x^N * f (x^(N+1)) + ∑ m ∈ Finset.range N, (x^m - x^(m+1)) * f (x^(m+1)) := by
      intro N
      induction N with
      | zero => simp; ring
      | succ N ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ N]
        simp only [pow_succ]
        ring
    have hterm : ∀ m : ℕ,
        F (x^m) - F (x^(m+1)) - (1 - x) * (f (x^m) - f (x^(m+1))) ≤ (x^m - x^(m+1)) * f (x^(m+1))
        ∧ (x^m - x^(m+1)) * f (x^(m+1)) ≤ F (x^m) - F (x^(m+1)) := by
      intro m
      have hle : x^(m+1) ≤ x^m := pow_le_pow_of_le_one hx0.le hx1.le (Nat.le_succ m)
      have h := hA _ _ (hpow (m+1)).le hle
      have hm := fmono _ _ (hpow (m+1)).le hle
      have hd2 : x^m - x^(m+1) ≤ 1 - x := by
        have : x^m - x^(m+1) = x^m * (1 - x) := by ring
        rw [this]
        have : x^m ≤ 1 := pow_le_one₀ hx0.le hx1.le
        nlinarith
      constructor
      · nlinarith [h.1, h.2]
      · linarith [h.1, h.2]
    have hT : ∀ N : ℕ,
        F 1 - F (x^N) - (1 - x) * (f 1 - f (x^N)) ≤ ∑ m ∈ Finset.range N, (x^m - x^(m+1)) * f (x^(m+1))
        ∧ ∑ m ∈ Finset.range N, (x^m - x^(m+1)) * f (x^(m+1)) ≤ F 1 - F (x^N) := by
      intro N
      have e1 := Finset.sum_range_sub' (fun m => F (x^m)) N
      have e2 := Finset.sum_range_sub' (fun m => f (x^m)) N
      simp only [pow_zero] at e1 e2
      constructor
      · calc _ = ∑ m ∈ Finset.range N, (F (x^m) - F (x^(m+1)) - (1 - x) * (f (x^m) - f (x^(m+1)))) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
          _ ≤ _ := Finset.sum_le_sum (fun m _ => (hterm m).1)
      · calc _ ≤ ∑ m ∈ Finset.range N, (F (x^m) - F (x^(m+1))) := Finset.sum_le_sum (fun m _ => (hterm m).2)
          _ = _ := e1
    have hP : ∀ N : ℕ, ∏ n ∈ Finset.range (N+1), ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (∑ n ∈ Finset.range (N+1), x^n * (f (x^(n+1)) - f (x^n))) := by
      intro N
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro n _
      have h1 : 0 < 1 + x^n := by linarith [hpow n]
      have h2 : 0 < 1 + x^(n+1) := by linarith [hpow (n+1)]
      rw [Real.rpow_def_of_pos (by positivity), Real.log_div h2.ne' h1.ne']
      congr 1
      simp only [hf]; ring
    have hlim : Tendsto (fun N : ℕ => ∏ n ∈ Finset.range (N+1), ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
        atTop (𝓝 (xprod x)) :=
      (hxprod x ⟨hx0, hx1⟩).comp (tendsto_add_atTop_nat 1)
    have hxN : Tendsto (fun N : ℕ => x^N) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hxN1 : Tendsto (fun N : ℕ => x^(N+1)) atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).2 hxN
    have hFN : Tendsto (fun N : ℕ => F (x^N)) atTop (𝓝 0) := by
      have := Fc.tendsto.comp hxN
      rwa [F0] at this
    have hfN : Tendsto (fun N : ℕ => f (x^N)) atTop (𝓝 0) := by
      have := fc.tendsto.comp hxN
      rwa [f0] at this
    have hfN1 : Tendsto (fun N : ℕ => f (x^(N+1))) atTop (𝓝 0) := by
      have := fc.tendsto.comp hxN1
      rwa [f0] at this
    have hg : Tendsto (fun N : ℕ => x^N * f (x^(N+1))) atTop (𝓝 0) := by
      simpa using hxN.mul hfN1
    have hLo : Tendsto (fun N : ℕ => Real.exp (-f 1 + x^N * f (x^(N+1)) + (F 1 - F (x^N) - (1 - x) * (f 1 - f (x^N)))))
        atTop (𝓝 (Real.exp (-f 1 + F 1 - (1 - x) * f 1))) := by
      apply (Real.continuous_exp.tendsto _).comp
      have := (((tendsto_const_nhds (x := -f 1)).add hg).add
        ((tendsto_const_nhds (x := F 1)).sub hFN |>.sub ((tendsto_const_nhds (x := (1-x))).mul
          ((tendsto_const_nhds (x := f 1)).sub hfN))))
      convert this using 2 <;> ring
    have hUp : Tendsto (fun N : ℕ => Real.exp (-f 1 + x^N * f (x^(N+1)) + (F 1 - F (x^N))))
        atTop (𝓝 (Real.exp (-f 1 + F 1))) := by
      apply (Real.continuous_exp.tendsto _).comp
      have := (((tendsto_const_nhds (x := -f 1)).add hg).add
        ((tendsto_const_nhds (x := F 1)).sub hFN))
      convert this using 2 <;> ring
    constructor
    · refine le_of_tendsto_of_tendsto hLo hlim (Filter.Eventually.of_forall fun N => ?_)
      dsimp only
      rw [hP, hform]
      apply Real.exp_le_exp.2
      linarith [(hT N).1]
    · refine le_of_tendsto_of_tendsto hlim hUp (Filter.Eventually.of_forall fun N => ?_)
      dsimp only
      rw [hP, hform]
      apply Real.exp_le_exp.2
      linarith [(hT N).2]
  have hval : Real.exp (-f 1 + F 1) = putnam_2004_b5_solution := by
    rw [F1, f1]
    have : -Real.log 2 + (2 * Real.log 2 - 1) = Real.log 2 - 1 := by ring
    rw [this, Real.exp_sub, Real.exp_log (by norm_num)]
  have hlo : Tendsto (fun x : ℝ => Real.exp (-f 1 + F 1 - (1 - x) * f 1)) (𝓝[<] 1)
      (𝓝 putnam_2004_b5_solution) := by
    rw [← hval]
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Real.continuous_exp.tendsto _).comp
    have : Continuous (fun x : ℝ => -f 1 + F 1 - (1 - x) * f 1) := by fun_prop
    have := this.tendsto 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo (tendsto_const_nhds) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx using (key x hx).1
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    rw [← hval]; exact (key x hx).2
