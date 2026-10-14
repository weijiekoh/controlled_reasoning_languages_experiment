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
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, ∀ v, H v = (1+v)*Real.log (1+v) - v :=
    ⟨fun v => (1+v)*Real.log (1+v) - v, fun v => rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ Af : ℝ → ℕ → ℝ, ∀ x N, Af x N =
      ∑ n ∈ Finset.range N, (x^n - x^(n+1)) * Real.log (1 + x^(n+1)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Lf, hLf⟩ : ∃ Lf : ℝ → ℝ, ∀ x, Lf x = ⨆ N, Af x N := ⟨_, fun _ => rfl⟩
  have hHfun : H = fun v => (1+v)*Real.log (1+v) - v := funext hH
  have hH0 : H 0 = 0 := by rw [hH]; simp
  have hH1 : H 1 = 2 * Real.log 2 - 1 := by rw [hH]; norm_num
  have hHc : ContinuousAt H 0 := by
    rw [hHfun]
    apply ContinuousAt.sub
    · exact ContinuousAt.mul (by fun_prop) (ContinuousAt.log (by fun_prop) (by norm_num))
    · fun_prop
  have hlogsub : ∀ a b : ℝ, 0 ≤ b → b ≤ a → Real.log (1+a) - Real.log (1+b) ≤ a - b := by
    intro a b hb hab
    have hpa : (0:ℝ) < 1 + a := by linarith
    have hpb : (0:ℝ) < 1 + b := by linarith
    have h1 : Real.log (1+a) - Real.log (1+b) = Real.log ((1+a)/(1+b)) := by
      rw [Real.log_div hpa.ne' hpb.ne']
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1+a)/(1+b) from div_pos hpa hpb)
    have h3 : (1+a)/(1+b) - 1 = (a-b)/(1+b) := by
      rw [div_sub_one hpb.ne']; congr 1; ring
    have h4 : (a-b)/(1+b) ≤ a-b := div_le_self (by linarith) (by linarith)
    linarith
  have hHlo : ∀ a b : ℝ, 0 ≤ b → b ≤ a → (a-b)*Real.log (1+b) ≤ H a - H b := by
    intro a b hb hab
    have hpa : (0:ℝ) < 1 + a := by linarith
    have hpb : (0:ℝ) < 1 + b := by linarith
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < (1+a)/(1+b) from div_pos hpa hpb)
    have h2 : Real.log ((1+a)/(1+b)) = Real.log (1+a) - Real.log (1+b) :=
      Real.log_div hpa.ne' hpb.ne'
    rw [h2] at h1
    have h4 := mul_le_mul_of_nonneg_left h1 hpa.le
    have h5 : (1+a) * (1 - ((1+a)/(1+b))⁻¹) = a - b := by
      rw [inv_div]; field_simp <;> ring
    rw [hH, hH]
    nlinarith [h4, h5]
  have hHup : ∀ a b : ℝ, 0 ≤ b → b ≤ a → H a - H b ≤ (a-b)*Real.log (1+a) := by
    intro a b hb hab
    have hpa : (0:ℝ) < 1 + a := by linarith
    have hpb : (0:ℝ) < 1 + b := by linarith
    have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (1+a)/(1+b) from div_pos hpa hpb)
    have h2 : Real.log ((1+a)/(1+b)) = Real.log (1+a) - Real.log (1+b) :=
      Real.log_div hpa.ne' hpb.ne'
    rw [h2] at h1
    have h4 := mul_le_mul_of_nonneg_left h1 hpb.le
    have h5 : (1+b) * ((1+a)/(1+b) - 1) = a - b := by
      field_simp <;> ring
    rw [hH, hH]
    nlinarith [h4, h5]
  have hHnn : ∀ v, 0 ≤ v → 0 ≤ H v := by
    intro v hv
    have := hHlo v 0 le_rfl hv
    rw [hH0] at this
    norm_num at this
    linarith
  have hAbound : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ N, H 1 - H (x^N) - (1-x) ≤ Af x N ∧
      Af x N ≤ H 1 - H (x^N) := by
    rintro x ⟨hx0, hx1⟩ N
    have hterm : ∀ n : ℕ, (H (x^n) - H (x^(n+1))) - (1-x)*(x^n - x^(n+1)) ≤
        (x^n - x^(n+1)) * Real.log (1 + x^(n+1)) ∧
        (x^n - x^(n+1)) * Real.log (1 + x^(n+1)) ≤ H (x^n) - H (x^(n+1)) := by
      intro n
      have hb0 : 0 ≤ x^(n+1) := pow_nonneg hx0.le _
      have hba : x^(n+1) ≤ x^n := by rw [pow_succ]; nlinarith [pow_nonneg hx0.le n]
      have ha1 : x^n ≤ 1 := pow_le_one₀ hx0.le hx1.le
      have hab_le : x^n - x^(n+1) ≤ 1 - x := by
        rw [pow_succ]; nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hx1.le)]
      have hL := hlogsub (x^n) (x^(n+1)) hb0 hba
      have hlo := hHlo (x^n) (x^(n+1)) hb0 hba
      have hup := hHup (x^n) (x^(n+1)) hb0 hba
      have hnn : 0 ≤ x^n - x^(n+1) := by linarith
      have e1 := mul_le_mul_of_nonneg_left hL hnn
      have e2 := mul_le_mul_of_nonneg_left hab_le hnn
      constructor
      · nlinarith [e1, e2, hup]
      · linarith
    have hsum := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => (hterm n).1)
    have hsum2 := Finset.sum_le_sum (fun n (_ : n ∈ Finset.range N) => (hterm n).2)
    have hd : ∑ n ∈ Finset.range N, (H (x^n) - H (x^(n+1))) = H (x^0) - H (x^N) :=
      Finset.sum_range_sub' (fun n => H (x^n)) N
    have hs : ∑ n ∈ Finset.range N, (x^n - x^(n+1)) = x^0 - x^N :=
      Finset.sum_range_sub' (fun n => x^n) N
    have hx0pow : x^0 = 1 := pow_zero x
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hd, hs, hx0pow] at hsum
    rw [hd, hx0pow] at hsum2
    rw [hAf]
    constructor
    · nlinarith [hsum, mul_nonneg (sub_nonneg.2 hx1.le) (pow_nonneg hx0.le N)]
    · linarith
  have hAle : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∀ N, Af x N ≤ 2 * Real.log 2 - 1 := by
    intro x hx N
    have h1 := (hAbound x hx N).2
    have h2 := hHnn (x^N) (pow_nonneg hx.1.le N)
    rw [hH1] at h1
    linarith
  have hHtend : ∀ x ∈ Set.Ioo (0:ℝ) 1, Tendsto (fun N => H (x^N)) atTop (𝓝 0) := by
    intro x hx
    have := hHc.tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one hx.1.le hx.2)
    rw [hH0] at this
    exact this
  have hconv : ∀ x ∈ Set.Ioo (0:ℝ) 1, Tendsto (Af x) atTop (𝓝 (Lf x)) := by
    intro x hx
    have hmono : Monotone (Af x) := by
      apply monotone_nat_of_le_succ
      intro N
      have hle : x^(N+1) ≤ x^N := by rw [pow_succ]; nlinarith [pow_nonneg hx.1.le N, hx.2]
      have hnn : 0 ≤ (x^N - x^(N+1)) * Real.log (1 + x^(N+1)) :=
        mul_nonneg (by linarith) (Real.log_nonneg (by linarith [pow_nonneg hx.1.le (N+1)]))
      simp only [hAf, Finset.sum_range_succ]
      linarith
    have hbdd : BddAbove (Set.range (Af x)) := ⟨2 * Real.log 2 - 1, by
      rintro _ ⟨N, rfl⟩
      exact hAle x hx N⟩
    rw [hLf]
    exact tendsto_atTop_ciSup hmono hbdd
  have hLge : ∀ x ∈ Set.Ioo (0:ℝ) 1, 2 * Real.log 2 - 1 - (1 - x) ≤ Lf x := by
    intro x hx
    have ht : Tendsto (fun N => H 1 - H (x^N) - (1-x)) atTop (𝓝 (H 1 - 0 - (1-x))) :=
      ((tendsto_const_nhds.sub (hHtend x hx)).sub tendsto_const_nhds)
    have := le_of_tendsto_of_tendsto' ht (hconv x hx) (fun N => (hAbound x hx N).1)
    rw [hH1] at this
    linarith
  have hfinal : ∀ x ∈ Set.Ioo (0:ℝ) 1, xprod x = Real.exp (Lf x + 0 - Real.log 2) := by
    intro x hx
    have hS : ∀ N, ∏ n ∈ Finset.range N, ((1 + x^(n+1))/(1+x^n))^(x^n) =
        Real.exp (Af x N + x^N * Real.log (1 + x^N) - Real.log 2) := by
      intro N
      have step1 : ∏ n ∈ Finset.range N, ((1 + x^(n+1))/(1+x^n))^(x^n) =
          ∏ n ∈ Finset.range N, Real.exp ((x^n) * (Real.log (1+x^(n+1)) - Real.log (1+x^n))) := by
        apply Finset.prod_congr rfl
        intro n _
        have p1 : 0 < 1 + x^(n+1) := by have := pow_pos hx.1 (n+1); linarith
        have p2 : 0 < 1 + x^n := by have := pow_pos hx.1 n; linarith
        rw [Real.rpow_def_of_pos (div_pos p1 p2), Real.log_div p1.ne' p2.ne']
        congr 1
        ring
      rw [step1, ← Real.exp_sum]
      congr 1
      have hid : ∀ N, ∑ n ∈ Finset.range N, (x^n) * (Real.log (1+x^(n+1)) - Real.log (1+x^n))
          = Af x N + x^N * Real.log (1+x^N) - Real.log 2 := by
        intro N
        induction N with
        | zero => norm_num [hAf]
        | succ k ih =>
          simp only [hAf, Finset.sum_range_succ] at ih ⊢
          rw [ih]
          ring
      exact hid N
    have h1 := hxprod x hx
    have hfun : (fun N => ∏ n ∈ Finset.range N, ((1 + x^(n+1))/(1+x^n))^(x^n)) =
        fun N => Real.exp (Af x N + x^N * Real.log (1+x^N) - Real.log 2) := funext hS
    rw [hfun] at h1
    have hctend : Tendsto (fun N => x^N * Real.log (1 + x^N)) atTop (𝓝 0) := by
      have hc : ContinuousAt (fun v : ℝ => v * Real.log (1+v)) 0 :=
        ContinuousAt.mul continuousAt_id (ContinuousAt.log (by fun_prop) (by norm_num))
      have := hc.tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one hx.1.le hx.2)
      rw [show (0:ℝ) = (fun v : ℝ => v * Real.log (1+v)) 0 by simp]
      exact this
    have hT : Tendsto (fun N => Real.exp (Af x N + x^N * Real.log (1+x^N) - Real.log 2)) atTop
        (𝓝 (Real.exp (Lf x + 0 - Real.log 2))) :=
      (Real.continuous_exp.tendsto _).comp
        (((hconv x hx).add hctend).sub tendsto_const_nhds)
    exact tendsto_nhds_unique h1 hT
  have hK : Tendsto Lf (𝓝[<] (1:ℝ)) (𝓝 (2 * Real.log 2 - 1)) := by
    have hlow : ∀ᶠ x in 𝓝[<] (1:ℝ), (2 * Real.log 2 - 1) - (1 - x) ≤ Lf x := by
      filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
      exact hLge x hx
    have hup : ∀ᶠ x in 𝓝[<] (1:ℝ), Lf x ≤ 2 * Real.log 2 - 1 := by
      filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
      rw [hLf]
      exact ciSup_le (fun N => hAle x hx N)
    have hlim_low : Tendsto (fun x : ℝ => (2 * Real.log 2 - 1) - (1 - x)) (𝓝[<] 1)
        (𝓝 (2 * Real.log 2 - 1)) := by
      have hc : Continuous (fun x : ℝ => (2 * Real.log 2 - 1) - (1 - x)) := by fun_prop
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
      simp only [sub_self, sub_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim_low tendsto_const_nhds hlow hup
  have hval : Real.exp (2 * Real.log 2 - 1 + 0 - Real.log 2) = 2 / Real.exp 1 := by
    rw [show 2 * Real.log 2 - 1 + 0 - Real.log 2 = Real.log 2 - 1 by ring, Real.exp_sub,
      Real.exp_log (by norm_num)]
  have hfin : Tendsto (fun x => Real.exp (Lf x + 0 - Real.log 2)) (𝓝[<] 1)
      (𝓝 (Real.exp (2 * Real.log 2 - 1 + 0 - Real.log 2))) :=
    (Real.continuous_exp.tendsto _).comp ((hK.add_const 0).sub_const (Real.log 2))
  rw [hval] at hfin
  show Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  apply hfin.congr'
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
  exact (hfinal x hx).symm
