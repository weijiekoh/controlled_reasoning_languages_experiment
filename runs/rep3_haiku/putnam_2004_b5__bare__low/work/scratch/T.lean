import Mathlib
open Nat Topology Filter
noncomputable abbrev putnam_2004_b5_solution : ℝ := 2 / Real.exp 1

lemma term_bound (x a : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (ha : 0 < a) (ha1 : a ≤ 1) :
    -((1 - x) * (a - a * x)) ≤ a * (Real.log (1 + a * x) - Real.log (1 + a))
      + (a - a * x) - (Real.log (1 + a) - Real.log (1 + a * x)) ∧
    a * (Real.log (1 + a * x) - Real.log (1 + a))
      + (a - a * x) - (Real.log (1 + a) - Real.log (1 + a * x)) ≤ 0 := by
  have hax : 0 < a * x := mul_pos ha hx0
  have hax' : a * x < a := by nlinarith
  have hp0 : 0 < 1 + a * x := by linarith
  have hq0 : 0 < 1 + a := by linarith
  have hpq : 1 + a * x < 1 + a := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hq0 hp0)
  rw [Real.log_div hp0.ne' hq0.ne'] at h1
  rw [Real.log_div hq0.ne' hp0.ne'] at h2
  have e1 : (1 + a) * ((1 + a * x) / (1 + a) - 1) = (1 + a * x) - (1 + a) := by
    field_simp
  have e2 : (1 + a * x) * ((1 + a) / (1 + a * x) - 1) = (1 + a) - (1 + a * x) := by
    field_simp
  have m1 := mul_le_mul_of_nonneg_left h1 hq0.le
  have m2 := mul_le_mul_of_nonneg_left h2 hp0.le
  set L := Real.log (1 + a) - Real.log (1 + a * x) with hL
  have hA : (1 + a) * L ≥ a - a * x := by nlinarith
  have hB : (1 + a * x) * L ≤ a - a * x := by nlinarith
  have hX : (a - a * x) - (1 + a) * L ≥ -(a - a*x)^2 := by
    nlinarith [mul_nonneg hq0.le hp0.le]
  have hE : (a - a*x)^2 ≤ (a - a*x) * (1 - x) := by
    have : a * (1 - x) ≤ 1 - x := by nlinarith
    nlinarith
  have expr : a * (Real.log (1 + a * x) - Real.log (1 + a))
      + (a - a * x) - (Real.log (1 + a) - Real.log (1 + a * x)) = (a - a*x) - (1 + a) * L := by
    rw [hL]; ring
  rw [expr]
  constructor
  · nlinarith
  · linarith

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
