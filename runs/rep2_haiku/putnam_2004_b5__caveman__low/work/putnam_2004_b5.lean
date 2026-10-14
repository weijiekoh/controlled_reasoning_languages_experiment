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
    ⟨_, fun t => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ → ℝ, ∀ x, T x = ∑' n : ℕ, x ^ n * Real.log (1 + x ^ n) :=
    ⟨_, fun x => rfl⟩
  have hFfun : F = fun t => (1 + t) * Real.log (1 + t) - t := funext hF
  have hFderiv : ∀ t : ℝ, -1 < t → HasDerivAt F (Real.log (1 + t)) t := by
    intro t ht
    have hne : (1 + t) ≠ 0 := ne_of_gt (by linarith)
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
      simpa using (hasDerivAt_id' t).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
      have := h1.log hne
      simpa using this
    have h3 : HasDerivAt (fun y : ℝ => (1 + y) * Real.log (1 + y) - y)
        (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1) t :=
      (h1.mul h2).sub (hasDerivAt_id' t)
    have e : 1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1 = Real.log (1 + t) := by
      rw [mul_one_div_cancel hne]
      ring
    rw [e] at h3
    rw [hFfun]
    exact h3
  have hbound : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (b - a) * Real.log (1 + a) ≤ F b - F a ∧ F b - F a ≤ (b - a) * Real.log (1 + b) := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h | h
    · subst h; simp
    · have hcont : ContinuousOn F (Set.Icc a b) := fun x hx =>
        (hFderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F (fun t => Real.log (1 + t)) h hcont
        (fun x hx => hFderiv x (by linarith [hx.1]))
      have hpos : 0 < b - a := by linarith
      rw [eq_div_iff hpos.ne'] at hceq
      have hl1 : Real.log (1 + a) ≤ Real.log (1 + c) :=
        Real.log_le_log (by linarith) (by linarith [hc.1])
      have hl2 : Real.log (1 + c) ≤ Real.log (1 + b) :=
        Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
      have m1 := mul_le_mul_of_nonneg_left hl1 hpos.le
      have m2 := mul_le_mul_of_nonneg_left hl2 hpos.le
      constructor <;> nlinarith
  have hterm : ∀ x : ℝ, 0 < x → x < 1 → ∀ n : ℕ,
      0 ≤ x ^ n ∧ x ^ n ≤ 1 ∧ Real.log (1 + x ^ n) ≤ x ^ n := by
    intro x hx0 hx1 n
    have h0 : 0 ≤ x ^ n := pow_nonneg hx0.le n
    have h1 : x ^ n ≤ 1 := pow_le_one₀ hx0.le hx1.le
    refine ⟨h0, h1, ?_⟩
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + x ^ n by linarith)
    linarith
  have hsumm : ∀ x : ℝ, 0 < x → x < 1 →
      Summable (fun n : ℕ => x ^ n * Real.log (1 + x ^ n)) := by
    intro x hx0 hx1
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_geometric_of_lt_one hx0.le hx1)
    · exact mul_nonneg (pow_nonneg hx0.le n)
        (Real.log_nonneg (by linarith [pow_nonneg hx0.le n]))
    · obtain ⟨h0, h1, h2⟩ := hterm x hx0 hx1 n
      nlinarith
  have hTp : ∀ x : ℝ, 0 < x → x < 1 →
      Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ n * Real.log (1 + x ^ n))
        atTop (𝓝 (T x)) := by
    intro x hx0 hx1
    rw [hT x]
    exact (hsumm x hx0 hx1).hasSum.tendsto_sum_nat
  have hA : ∀ x : ℝ, 0 < x → x < 1 → ∀ N : ℕ,
      x * (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)))
        = (∑ n ∈ Finset.range (N + 1), x ^ n * Real.log (1 + x ^ n)) - Real.log 2
          - x * (∑ n ∈ Finset.range N, x ^ n * Real.log (1 + x ^ n)) := by
    intro x hx0 hx1 N
    induction N with
    | zero => norm_num [Finset.sum_range_one]
    | succ k ih =>
      simp only [Finset.sum_range_succ] at ih ⊢
      linear_combination ih
  have hA' : ∀ x : ℝ, 0 < x → x < 1 → ∀ N : ℕ,
      (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)))
        = x⁻¹ * ((∑ n ∈ Finset.range (N + 1), x ^ n * Real.log (1 + x ^ n)) - Real.log 2
          - x * (∑ n ∈ Finset.range N, x ^ n * Real.log (1 + x ^ n))) := by
    intro x hx0 hx1 N
    rw [← hA x hx0 hx1 N, ← mul_assoc, inv_mul_cancel₀ hx0.ne', one_mul]
  have hAlim : ∀ x : ℝ, 0 < x → x < 1 →
      Tendsto (fun N : ℕ =>
        ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)))
        atTop (𝓝 (x⁻¹ * ((1 - x) * T x - Real.log 2))) := by
    intro x hx0 hx1
    have h1 := hTp x hx0 hx1
    have h2 : Tendsto (fun N : ℕ => x⁻¹ * ((∑ n ∈ Finset.range (N + 1), x ^ n * Real.log (1 + x ^ n))
          - Real.log 2 - x * (∑ n ∈ Finset.range N, x ^ n * Real.log (1 + x ^ n))))
        atTop (𝓝 (x⁻¹ * (T x - Real.log 2 - x * T x))) := by
      apply Tendsto.const_mul
      apply Tendsto.sub
      · exact (h1.comp (tendsto_add_atTop_nat 1)).sub_const _
      · exact h1.const_mul _
    have e : x⁻¹ * (T x - Real.log 2 - x * T x) = x⁻¹ * ((1 - x) * T x - Real.log 2) := by ring
    rw [e] at h2
    exact Tendsto.congr (fun N => (hA' x hx0 hx1 N).symm) h2
  have hprod : ∀ x : ℝ, 0 < x → x < 1 → ∀ N : ℕ,
      ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (∑ n ∈ Finset.range N,
            x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
    intro x hx0 hx1 N
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro n _
    have hp : ∀ m : ℕ, 0 < 1 + x ^ m := fun m => by linarith [pow_nonneg hx0.le m]
    rw [Real.rpow_def_of_pos (div_pos (hp (n + 1)) (hp n)),
      Real.log_div (hp (n + 1)).ne' (hp n).ne']
    congr 1
    ring
  have hmain : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      xprod x = Real.exp (x⁻¹ * ((1 - x) * T x - Real.log 2)) := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hlim : Tendsto (fun N : ℕ =>
        ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)) atTop
        (𝓝 (Real.exp (x⁻¹ * ((1 - x) * T x - Real.log 2)))) := by
      have e : (fun N : ℕ => ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
          = fun N : ℕ => Real.exp (∑ n ∈ Finset.range N,
              x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) :=
        funext (hprod x hx0 hx1)
      rw [e]
      exact (Real.continuous_exp.tendsto _).comp (hAlim x hx0 hx1)
    exact tendsto_nhds_unique (hxprod x ⟨hx0, hx1⟩) hlim
  have hsq : ∀ x : ℝ, 0 < x → x < 1 →
      F 1 ≤ (1 - x) * T x ∧ (1 - x) * T x ≤ F 1 + (1 - x) * Real.log 2 := by
    intro x hx0 hx1
    have hp : ∀ m : ℕ, 0 ≤ x ^ m := fun m => pow_nonneg hx0.le m
    have hterm2 : ∀ n : ℕ,
        0 ≤ (1 - x) * (x ^ n * Real.log (1 + x ^ n)) - (F (x ^ n) - F (x ^ (n + 1))) ∧
        (1 - x) * (x ^ n * Real.log (1 + x ^ n)) - (F (x ^ n) - F (x ^ (n + 1)))
          ≤ (1 - x) * (Real.log (1 + x ^ n) - Real.log (1 + x ^ (n + 1))) := by
      intro n
      have hab : x ^ (n + 1) ≤ x ^ n := pow_le_pow_of_le_one hx0.le hx1.le (Nat.le_succ n)
      obtain ⟨hl, hr⟩ := hbound (x ^ (n + 1)) (x ^ n) (hp _) hab
      have hdiff : x ^ n - x ^ (n + 1) = (1 - x) * x ^ n := by ring
      rw [hdiff] at hl hr
      have hn1 : x ^ n ≤ 1 := pow_le_one₀ hx0.le hx1.le
      have hmono : Real.log (1 + x ^ (n + 1)) ≤ Real.log (1 + x ^ n) :=
        Real.log_le_log (by linarith [hp (n + 1)]) (by linarith)
      have hw : 0 ≤ (1 - x) * (1 - x ^ n) * (Real.log (1 + x ^ n) - Real.log (1 + x ^ (n + 1))) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      constructor
      · nlinarith
      · nlinarith
    have hW : ∀ N : ℕ,
        0 ≤ (∑ n ∈ Finset.range N, (1 - x) * (x ^ n * Real.log (1 + x ^ n)))
          - (∑ n ∈ Finset.range N, (F (x ^ n) - F (x ^ (n + 1))))
        ∧ (∑ n ∈ Finset.range N, (1 - x) * (x ^ n * Real.log (1 + x ^ n)))
          - (∑ n ∈ Finset.range N, (F (x ^ n) - F (x ^ (n + 1))))
          ≤ (1 - x) * (Real.log (1 + x ^ 0) - Real.log (1 + x ^ N)) := by
      intro N
      rw [← Finset.sum_sub_distrib]
      have htel : ∑ n ∈ Finset.range N, (Real.log (1 + x ^ n) - Real.log (1 + x ^ (n + 1)))
          = Real.log (1 + x ^ 0) - Real.log (1 + x ^ N) :=
        Finset.sum_range_sub' (fun i => Real.log (1 + x ^ i)) N
      have hmul : ∑ n ∈ Finset.range N, (1 - x) * (Real.log (1 + x ^ n) - Real.log (1 + x ^ (n + 1)))
          = (1 - x) * (Real.log (1 + x ^ 0) - Real.log (1 + x ^ N)) := by
        rw [← htel, Finset.mul_sum]
      constructor
      · exact Finset.sum_nonneg (fun n _ => (hterm2 n).1)
      · rw [← hmul]
        exact Finset.sum_le_sum (fun n _ => (hterm2 n).2)
    have hV : ∀ N : ℕ, ∑ n ∈ Finset.range N, (F (x ^ n) - F (x ^ (n + 1)))
        = F 1 - F (x ^ N) := by
      intro N
      have h := Finset.sum_range_sub' (fun i : ℕ => F (x ^ i)) N
      simp only [pow_zero] at h
      exact h
    have hW' : ∀ N : ℕ,
        0 ≤ (∑ n ∈ Finset.range N, (1 - x) * (x ^ n * Real.log (1 + x ^ n)))
          - (F 1 - F (x ^ N)) ∧
        (∑ n ∈ Finset.range N, (1 - x) * (x ^ n * Real.log (1 + x ^ n)))
          - (F 1 - F (x ^ N)) ≤ (1 - x) * Real.log 2 := by
      intro N
      rw [← hV N]
      obtain ⟨h1, h2⟩ := hW N
      refine ⟨h1, ?_⟩
      have hlN : 0 ≤ Real.log (1 + x ^ N) := Real.log_nonneg (by linarith [hp N])
      have hc : Real.log (1 + x ^ 0) = Real.log 2 := by norm_num
      rw [hc] at h2
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) hlN
      linarith
    have hUlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 - x) * (x ^ n * Real.log (1 + x ^ n)))
        atTop (𝓝 ((1 - x) * T x)) := by
      have e : (fun N : ℕ => ∑ n ∈ Finset.range N, (1 - x) * (x ^ n * Real.log (1 + x ^ n)))
          = fun N : ℕ => (1 - x) * ∑ n ∈ Finset.range N, x ^ n * Real.log (1 + x ^ n) := by
        funext N
        rw [Finset.mul_sum]
      rw [e]
      exact (hTp x hx0 hx1).const_mul (1 - x)
    have hVlim : Tendsto (fun N : ℕ => F 1 - F (x ^ N)) atTop (𝓝 (F 1 - F 0)) := by
      have hFx : Tendsto (fun N : ℕ => F (x ^ N)) atTop (𝓝 (F 0)) :=
        ((hFderiv 0 (by norm_num)).continuousAt.tendsto).comp
          (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1)
      exact tendsto_const_nhds.sub hFx
    have hF0 : F 0 = 0 := by rw [hF]; simp
    rw [hF0, sub_zero] at hVlim
    have hlim := hUlim.sub hVlim
    have hlow := ge_of_tendsto hlim (Filter.Eventually.of_forall fun N => (hW' N).1)
    have hup := le_of_tendsto hlim (Filter.Eventually.of_forall fun N => (hW' N).2)
    constructor <;> linarith
  have hKlim : Tendsto (fun x : ℝ => (1 - x) * T x) (𝓝[<] 1) (𝓝 (F 1)) := by
    have hev : ∀ᶠ x in 𝓝[<] (1:ℝ), 0 < x ∧ x < 1 := by
      filter_upwards [Ioo_mem_nhdsLT_of_mem (show (1:ℝ) ∈ Set.Ioc 0 1 by norm_num)] with x hx
      exact hx
    have hlo : Tendsto (fun _ : ℝ => F 1) (𝓝[<] 1) (𝓝 (F 1)) := tendsto_const_nhds
    have hcont : Continuous (fun x : ℝ => F 1 + (1 - x) * Real.log 2) := by fun_prop
    have hhi : Tendsto (fun x : ℝ => F 1 + (1 - x) * Real.log 2) (𝓝[<] 1) (𝓝 (F 1)) := by
      have h : Tendsto (fun x : ℝ => F 1 + (1 - x) * Real.log 2) (𝓝[<] 1)
          (𝓝 (F 1 + (1 - 1) * Real.log 2)) := tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto 1)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (by filter_upwards [hev] with x hx; exact (hsq x hx.1 hx.2).1)
      (by filter_upwards [hev] with x hx; exact (hsq x hx.1 hx.2).2)
  have hLlim : Tendsto (fun x : ℝ => x⁻¹ * ((1 - x) * T x - Real.log 2))
      (𝓝[<] 1) (𝓝 (Real.log 2 - 1)) := by
    have hid : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hinv := hid.inv₀ one_ne_zero
    have h := hinv.mul (hKlim.sub_const (Real.log 2))
    have h2 : (1:ℝ) + 1 = 2 := by norm_num
    have e : (1:ℝ)⁻¹ * (F 1 - Real.log 2) = Real.log 2 - 1 := by
      rw [inv_one, hF 1, h2]
      ring
    rw [e] at h
    exact h
  have hfin : Tendsto (fun x : ℝ => Real.exp (x⁻¹ * ((1 - x) * T x - Real.log 2)))
      (𝓝[<] 1) (𝓝 (Real.exp (Real.log 2 - 1))) :=
    (Real.continuous_exp.tendsto _).comp hLlim
  have hev : ∀ᶠ x in 𝓝[<] (1:ℝ), x ∈ Set.Ioo (0:ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT_of_mem (show (1:ℝ) ∈ Set.Ioc 0 1 by norm_num)] with x hx
    exact hx
  have heq : (fun x : ℝ => Real.exp (x⁻¹ * ((1 - x) * T x - Real.log 2)))
      =ᶠ[𝓝[<] 1] xprod := by
    filter_upwards [hev] with x hx
    exact (hmain x hx).symm
  have hsol : Real.exp (Real.log 2 - 1) = putnam_2004_b5_solution := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  rw [← hsol]
  exact Tendsto.congr' heq hfin
