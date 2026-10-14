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
  have hL : ∀ p q : ℝ, 0 < q → q ≤ p →
      (p - q) / (1 + p) ≤ Real.log (1 + p) - Real.log (1 + q) ∧
      Real.log (1 + p) - Real.log (1 + q) ≤ (p - q) / (1 + q) := by
    intro p q hq hqp
    have h1 : 0 < 1 + q := by linarith
    have h2 : 0 < 1 + p := by linarith
    have hlog : Real.log (1 + p) - Real.log (1 + q) = Real.log ((1 + p) / (1 + q)) := by
      rw [Real.log_div h2.ne' h1.ne']
    rw [hlog]
    have hy : 0 < (1 + p) / (1 + q) := div_pos h2 h1
    have u := Real.log_le_sub_one_of_pos hy
    have v := Real.one_sub_inv_le_log_of_pos hy
    constructor
    · have e : 1 - ((1 + p) / (1 + q))⁻¹ = (p - q) / (1 + p) := by
        field_simp
        ring
      linarith
    · have e : (1 + p) / (1 + q) - 1 = (p - q) / (1 + q) := by
        field_simp
        ring
      linarith
  have hterm : ∀ p q x : ℝ, 0 < x → x < 1 → 0 < q → q = x * p → p ≤ 1 → 0 < p →
      p * (Real.log (1 + q) - Real.log (1 + p)) + ((p - Real.log (1 + p)) - (q - Real.log (1 + q))) ≤ 0 ∧
      -((1 - x) * (p - q)) ≤ p * (Real.log (1 + q) - Real.log (1 + p)) + ((p - Real.log (1 + p)) - (q - Real.log (1 + q))) := by
    intro p q x hx0 hx1 hq hqx hp1 hp
    have hqp : q ≤ p := by rw [hqx]; nlinarith
    obtain ⟨A, B⟩ := hL p q hq hqp
    have hD0 : 0 ≤ Real.log (1 + p) - Real.log (1 + q) := by
      have := Real.log_le_log (by linarith) (by linarith : 1 + q ≤ 1 + p)
      linarith
    have A' : p - q ≤ (Real.log (1 + p) - Real.log (1 + q)) * (1 + p) := by
      rw [div_le_iff₀ (by linarith)] at A; linarith
    have B' : (Real.log (1 + p) - Real.log (1 + q)) * (1 + q) ≤ p - q := by
      rw [le_div_iff₀ (by linarith)] at B; linarith
    have hDp : Real.log (1 + p) - Real.log (1 + q) ≤ p - q := by nlinarith
    have hpq : p - q ≤ 1 - x := by rw [hqx]; nlinarith
    have E : p * (Real.log (1 + q) - Real.log (1 + p)) + ((p - Real.log (1 + p)) - (q - Real.log (1 + q)))
        = (p - q) - (Real.log (1 + p) - Real.log (1 + q)) * (1 + p) := by ring
    rw [E]
    have hpq0 : 0 ≤ p - q := by linarith
    constructor
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left hDp hpq0, mul_le_mul_of_nonneg_left hpq hpq0]
  have key : ∀ x : ℝ, 0 < x → x < 1 →
      Real.exp (0 - (1 - Real.log 2) - (1 - x)) ≤ xprod x ∧ xprod x ≤ Real.exp (0 - (1 - Real.log 2)) := by
    intro x hx0 hx1
    have hfac : ∀ N : ℕ, ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
      intro N
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro n _
      have h1 : 0 < 1 + x ^ (n + 1) := by have := pow_pos hx0 (n + 1); linarith
      have h2 : 0 < 1 + x ^ n := by have := pow_pos hx0 n; linarith
      rw [Real.rpow_def_of_pos (div_pos h1 h2), Real.log_div h1.ne' h2.ne']
      congr 1; ring
    have hS := hxprod x ⟨hx0, hx1⟩
    simp only [hfac] at hS
    have hbounds : ∀ N : ℕ,
        ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))
          ≤ (x ^ N - Real.log (1 + x ^ N)) - (1 - Real.log 2) ∧
        (x ^ N - Real.log (1 + x ^ N)) - (1 - Real.log 2) - (1 - x)
          ≤ ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)) := by
      intro N
      have hT : ∑ n ∈ Finset.range N, (x ^ n - x ^ (n + 1)) = 1 - x ^ N := by
        have := Finset.sum_range_sub' (fun n : ℕ => x ^ n) N
        simpa [Function.comp_def] using this
      have hW : ∑ n ∈ Finset.range N, ((x ^ n - Real.log (1 + x ^ n)) - (x ^ (n + 1) - Real.log (1 + x ^ (n + 1))))
          = (x ^ 0 - Real.log (1 + x ^ 0)) - (x ^ N - Real.log (1 + x ^ N)) :=
        Finset.sum_range_sub' (fun n : ℕ => x ^ n - Real.log (1 + x ^ n)) N
      have h0 : x ^ 0 - Real.log (1 + x ^ 0) = 1 - Real.log 2 := by norm_num
      rw [h0] at hW
      have hU : ∑ n ∈ Finset.range N, (x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))
          + ((x ^ n - Real.log (1 + x ^ n)) - (x ^ (n + 1) - Real.log (1 + x ^ (n + 1))))) ≤ 0 :=
        Finset.sum_nonpos (fun n _ => (hterm (x ^ n) (x ^ (n + 1)) x hx0 hx1 (pow_pos hx0 _)
          (by ring) (pow_le_one₀ hx0.le hx1.le) (pow_pos hx0 _)).1)
      have hLo : ∑ n ∈ Finset.range N, -((1 - x) * (x ^ n - x ^ (n + 1))) ≤ ∑ n ∈ Finset.range N, (x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))
          + ((x ^ n - Real.log (1 + x ^ n)) - (x ^ (n + 1) - Real.log (1 + x ^ (n + 1))))) :=
        Finset.sum_le_sum (fun n _ => (hterm (x ^ n) (x ^ (n + 1)) x hx0 hx1 (pow_pos hx0 _)
          (by ring) (pow_le_one₀ hx0.le hx1.le) (pow_pos hx0 _)).2)
      have e : ∑ n ∈ Finset.range N, -((1 - x) * (x ^ n - x ^ (n + 1))) = -((1 - x) * (1 - x ^ N)) := by
        rw [← hT, Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hnn : 0 ≤ (1 - x) * x ^ N := mul_nonneg (by linarith) (pow_pos hx0 N).le
      rw [Finset.sum_add_distrib, hW] at hU
      rw [e, Finset.sum_add_distrib, hW] at hLo
      constructor
      · nlinarith
      · nlinarith
    have hpow : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hcont : ContinuousAt (fun t : ℝ => t - Real.log (1 + t)) 0 := by
      apply ContinuousAt.sub continuousAt_id
      apply ContinuousAt.log (by fun_prop) (by norm_num)
    have hgN : Tendsto (fun N : ℕ => x ^ N - Real.log (1 + x ^ N)) atTop (𝓝 0) := by
      have := hcont.tendsto.comp hpow
      simpa [Function.comp_def] using this
    have hUpper : Tendsto (fun N : ℕ => Real.exp ((x ^ N - Real.log (1 + x ^ N)) - (1 - Real.log 2)))
        atTop (𝓝 (Real.exp (0 - (1 - Real.log 2)))) := (Real.continuous_exp.tendsto _).comp (hgN.sub_const _)
    have hLower : Tendsto (fun N : ℕ => Real.exp ((x ^ N - Real.log (1 + x ^ N)) - (1 - Real.log 2) - (1 - x)))
        atTop (𝓝 (Real.exp (0 - (1 - Real.log 2) - (1 - x)))) := (Real.continuous_exp.tendsto _).comp ((hgN.sub_const _).sub_const _)
    constructor
    · exact le_of_tendsto_of_tendsto' hLower hS (fun N => Real.exp_le_exp.mpr (hbounds N).2)
    · exact le_of_tendsto_of_tendsto' hS hUpper (fun N => Real.exp_le_exp.mpr (hbounds N).1)
  have E1 : Real.exp (0 - (1 - Real.log 2)) = 2 / Real.exp 1 := by
    rw [show (0:ℝ) - (1 - Real.log 2) = Real.log 2 - 1 by ring, Real.exp_sub, Real.exp_log two_pos]
  have hc : Continuous (fun x : ℝ => Real.exp (0 - (1 - Real.log 2) - (1 - x))) := by fun_prop
  have hlo := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
  have e2 : (0:ℝ) - (1 - Real.log 2) - (1 - 1) = 0 - (1 - Real.log 2) := by ring
  rw [e2, E1] at hlo
  have hup : Tendsto (fun _ : ℝ => 2 / Real.exp 1) (𝓝[<] 1) (𝓝 (2 / Real.exp 1)) := tendsto_const_nhds
  show Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with x hx
    exact (key x hx.1 hx.2).1
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with x hx
    rw [← E1]
    exact (key x hx.1 hx.2).2
