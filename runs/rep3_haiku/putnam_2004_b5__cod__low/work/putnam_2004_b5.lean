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
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      Real.log (1+a) * (b-a) ≤ ((1+b)*Real.log (1+b) - b) - ((1+a)*Real.log (1+a) - a) ∧
      ((1+b)*Real.log (1+b) - b) - ((1+a)*Real.log (1+a) - a) ≤ Real.log (1+b) * (b-a) := by
    intro a b ha hab
    have hA : 0 < 1 + a := by linarith
    have hB : 0 < 1 + b := by linarith
    have hlog : Real.log (1+b) - Real.log (1+a) = Real.log ((1+b)/(1+a)) :=
      (Real.log_div hB.ne' hA.ne').symm
    have h2 : Real.log ((1+b)/(1+a)) ≤ (1+b)/(1+a) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hB hA)
    have h3 : 1 - ((1+b)/(1+a))⁻¹ ≤ Real.log ((1+b)/(1+a)) :=
      Real.one_sub_inv_le_log_of_pos (div_pos hB hA)
    have e1 : ((1+b)/(1+a) - 1) * (1+a) = b - a := by
      field_simp
      ring
    have e2 : (1 - ((1+b)/(1+a))⁻¹) * (1+b) = b - a := by
      field_simp
      ring
    have k1 : b - a ≤ (Real.log (1+b) - Real.log (1+a)) * (1+b) := by
      rw [← e2, hlog]; exact mul_le_mul_of_nonneg_right h3 hB.le
    have k2 : (Real.log (1+b) - Real.log (1+a)) * (1+a) ≤ b - a := by
      rw [hlog, ← e1]; exact mul_le_mul_of_nonneg_right h2 hA.le
    constructor <;> nlinarith [k1, k2]
  have hbnd : ∀ x : ℝ, 0 < x → x < 1 →
      Real.exp ((Real.log 2 - 1)/x) ≤ xprod x ∧
      xprod x ≤ Real.exp ((Real.log 2 - 1 + (1-x)*Real.log 2)/x) := by
    intro x hx0 hx1
    have hprod : ∀ N : ℕ, ∏ n ∈ Finset.range N, ((1 + x^(n+1))/(1+x^n))^(x^n) =
        Real.exp (∑ n ∈ Finset.range N, x^n * (Real.log (1+x^(n+1)) - Real.log (1+x^n))) := by
      intro N
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro n _
      have hpa : 0 < 1 + x^(n+1) := by linarith [pow_nonneg hx0.le (n+1)]
      have hpb : 0 < 1 + x^n := by linarith [pow_nonneg hx0.le n]
      have hp : 0 < (1+x^(n+1))/(1+x^n) := div_pos hpa hpb
      rw [Real.rpow_def_of_pos hp, Real.log_div hpa.ne' hpb.ne']
      congr 1
      ring
    have hid : ∀ N : ℕ, x * (∑ n ∈ Finset.range N, x^n * (Real.log (1+x^(n+1)) - Real.log (1+x^n))) =
        -Real.log 2 + x^N * Real.log (1+x^N) +
          ∑ m ∈ Finset.range N, (x^m - x^(m+1)) * Real.log (1+x^m) := by
      intro N
      induction N with
      | zero => norm_num
      | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linear_combination ih
    have hbd : ∀ N : ℕ,
        ((1+1)*Real.log (1+1) - 1) - ((1+x^N)*Real.log (1+x^N) - x^N) ≤
          ∑ m ∈ Finset.range N, (x^m - x^(m+1)) * Real.log (1+x^m) ∧
        ∑ m ∈ Finset.range N, (x^m - x^(m+1)) * Real.log (1+x^m) ≤
          ((1+1)*Real.log (1+1) - 1) - ((1+x^N)*Real.log (1+x^N) - x^N) +
            (1-x)*(Real.log (1+1) - Real.log (1+x^N)) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hle : x^(N+1) ≤ x^N := pow_le_pow_of_le_one hx0.le hx1.le (Nat.le_succ N)
        have hpos : 0 ≤ x^(N+1) := pow_nonneg hx0.le _
        obtain ⟨t1, t2⟩ := key (x^(N+1)) (x^N) hpos hle
        have hm : x^N ≤ 1 := pow_le_one₀ hx0.le hx1.le
        have hsucc : x^(N+1) = x^N * x := pow_succ x N
        have hLle : Real.log (1+x^(N+1)) ≤ Real.log (1+x^N) :=
          Real.log_le_log (by linarith) (by linarith)
        have hd : x^N - x^(N+1) ≤ 1 - x := by
          rw [hsucc]
          nlinarith [mul_nonneg (sub_nonneg.2 hx1.le) (sub_nonneg.2 hm)]
        have t3 : (x^N - x^(N+1)) * (Real.log (1+x^N) - Real.log (1+x^(N+1))) ≤
            (1-x) * (Real.log (1+x^N) - Real.log (1+x^(N+1))) :=
          mul_le_mul_of_nonneg_right hd (by linarith)
        rw [Finset.sum_range_succ]
        constructor <;> linarith [t1, t2, t3, ih1, ih2]
    obtain ⟨Fl, hFl⟩ : ∃ Fl : ℝ → ℝ, Fl = fun u => (-Real.log 2 + u * Real.log (1+u) +
        ((1+1)*Real.log (1+1) - 1) - ((1+u)*Real.log (1+u) - u)) / x := ⟨_, rfl⟩
    obtain ⟨Fu, hFu⟩ : ∃ Fu : ℝ → ℝ, Fu = fun u => (-Real.log 2 + u * Real.log (1+u) +
        ((1+1)*Real.log (1+1) - 1) - ((1+u)*Real.log (1+u) - u) +
          (1-x)*(Real.log (1+1) - Real.log (1+u))) / x := ⟨_, rfl⟩
    have hL : ContinuousAt (fun u : ℝ => Real.log (1+u)) 0 :=
      ContinuousAt.log (by fun_prop) (by norm_num)
    have hFlc : ContinuousAt Fl 0 := by rw [hFl]; fun_prop
    have hFuc : ContinuousAt Fu 0 := by rw [hFu]; fun_prop
    have hu : Filter.Tendsto (fun N : ℕ => x^N) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hlo : Filter.Tendsto (fun N : ℕ => Real.exp (Fl (x^N))) Filter.atTop
        (𝓝 (Real.exp (Fl 0))) :=
      (Real.continuous_exp.tendsto _).comp (hFlc.tendsto.comp hu)
    have hhi : Filter.Tendsto (fun N : ℕ => Real.exp (Fu (x^N))) Filter.atTop
        (𝓝 (Real.exp (Fu 0))) :=
      (Real.continuous_exp.tendsto _).comp (hFuc.tendsto.comp hu)
    have hxp : Filter.Tendsto (fun N : ℕ => Real.exp (∑ n ∈ Finset.range N,
        x^n * (Real.log (1+x^(n+1)) - Real.log (1+x^n)))) Filter.atTop (𝓝 (xprod x)) := by
      have h := hxprod x ⟨hx0, hx1⟩
      have hfun : (fun N : ℕ => ∏ n ∈ Finset.range N, ((1 + x^(n+1))/(1+x^n))^(x^n)) =
          fun N : ℕ => Real.exp (∑ n ∈ Finset.range N,
            x^n * (Real.log (1+x^(n+1)) - Real.log (1+x^n))) := funext hprod
      rw [hfun] at h
      exact h
    have lowerB : ∀ N : ℕ, Fl (x^N) ≤ ∑ n ∈ Finset.range N,
        x^n * (Real.log (1+x^(n+1)) - Real.log (1+x^n)) := by
      intro N
      rw [hFl]
      dsimp only
      rw [div_le_iff₀ hx0]
      have := hid N
      have := hbd N
      linarith
    have upperB : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        x^n * (Real.log (1+x^(n+1)) - Real.log (1+x^n)) ≤ Fu (x^N) := by
      intro N
      rw [hFu]
      dsimp only
      rw [le_div_iff₀ hx0]
      have := hid N
      have := hbd N
      linarith
    have hlow : Real.exp (Fl 0) ≤ xprod x :=
      le_of_tendsto_of_tendsto' hlo hxp (fun N => Real.exp_le_exp.2 (lowerB N))
    have hup : xprod x ≤ Real.exp (Fu 0) :=
      le_of_tendsto_of_tendsto' hxp hhi (fun N => Real.exp_le_exp.2 (upperB N))
    have h11 : (1:ℝ) + 1 = 2 := by norm_num
    have h10 : (1:ℝ) + 0 = 1 := by norm_num
    have v1 : Fl 0 = (Real.log 2 - 1)/x := by
      rw [hFl]
      dsimp only
      rw [h11, h10, Real.log_one]
      congr 1
      ring
    have v2 : Fu 0 = (Real.log 2 - 1 + (1-x)*Real.log 2)/x := by
      rw [hFu]
      dsimp only
      rw [h11, h10, Real.log_one]
      congr 1
      ring
    rw [v1] at hlow
    rw [v2] at hup
    exact ⟨hlow, hup⟩
  have hF : Filter.Tendsto (fun x : ℝ => Real.exp ((Real.log 2 - 1)/x)) (𝓝[<] 1)
      (𝓝 (2 / Real.exp 1)) := by
    have hval : Real.exp ((Real.log 2 - 1)/1) = 2 / Real.exp 1 := by
      rw [div_one, Real.exp_sub, Real.exp_log two_pos]
    have hc : ContinuousAt (fun x : ℝ => Real.exp ((Real.log 2 - 1)/x)) 1 :=
      Real.continuous_exp.continuousAt.comp (f := fun x : ℝ => (Real.log 2 - 1)/x)
        (continuousAt_const.div continuousAt_id one_ne_zero)
    rw [← hval]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hH : Filter.Tendsto (fun x : ℝ => Real.exp ((Real.log 2 - 1 + (1-x)*Real.log 2)/x))
      (𝓝[<] 1) (𝓝 (2 / Real.exp 1)) := by
    have hval : Real.exp ((Real.log 2 - 1 + (1-1)*Real.log 2)/1) = 2 / Real.exp 1 := by
      rw [div_one, sub_self, zero_mul, add_zero, Real.exp_sub, Real.exp_log two_pos]
    have hc : ContinuousAt (fun x : ℝ => Real.exp ((Real.log 2 - 1 + (1-x)*Real.log 2)/x)) 1 :=
      Real.continuous_exp.continuousAt.comp
        (f := fun x : ℝ => (Real.log 2 - 1 + (1-x)*Real.log 2)/x)
        ((continuousAt_const.add ((continuousAt_const.sub continuousAt_id).mul
          continuousAt_const)).div continuousAt_id one_ne_zero)
    rw [← hval]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  show Filter.Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hF hH ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    exact (hbnd x hx.1 hx.2).1
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    exact (hbnd x hx.1 hx.2).2
