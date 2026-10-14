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
  obtain ⟨ph, hph⟩ : ∃ ph : ℝ → ℝ, ∀ t, ph t = Real.log (1 + t) :=
    ⟨fun t => Real.log (1 + t), fun t => rfl⟩
  have hphcont : ContinuousOn ph (Set.Icc 0 1) := by
    have e : ph = fun t => Real.log (1 + t) := funext hph
    rw [e]
    exact ContinuousOn.log (by fun_prop) (fun t ht => ne_of_gt (by linarith [ht.1]))
  have hint : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      IntervalIntegrable ph MeasureTheory.volume a b := by
    intro a b ha1 ha2 hb1 hb2
    exact (hphcont.mono (Set.uIcc_subset_Icc ⟨ha1, ha2⟩ ⟨hb1, hb2⟩)).intervalIntegrable
  have hL1 : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ph b - ph a ≤ b - a := by
    intro a b ha hab
    rw [hph, hph]
    have hb : (0:ℝ) < 1 + b := by linarith
    have ha' : (0:ℝ) < 1 + a := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos hb ha')
    rw [Real.log_div hb.ne' ha'.ne'] at h
    have h2 : (1 + b) / (1 + a) - 1 ≤ b - a := by
      rw [div_sub_one ha'.ne', div_le_iff₀ ha']
      nlinarith [mul_nonneg (sub_nonneg.2 hab) ha]
    linarith
  have hL2 : ∀ b : ℝ, 0 ≤ b → ph b ≤ b := by
    intro b hb
    rw [hph]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + b by linarith)
    linarith
  have hL0 : ph 0 = 0 := by rw [hph]; simp
  have hLnn : ∀ b : ℝ, 0 ≤ b → 0 ≤ ph b := by
    intro b hb; rw [hph]; exact Real.log_nonneg (by linarith)
  have hLmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ph a ≤ ph b := by
    intro a b ha hab; rw [hph, hph]
    exact Real.log_le_log (by linarith) (by linarith)
  have hLI : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      ph a * (b - a) ≤ ∫ t in a..b, ph t ∧ ∫ t in a..b, ph t ≤ ph b * (b - a) := by
    intro a b ha hab hb1
    have hi := hint a b ha (by linarith) (by linarith) hb1
    constructor
    · have h1 : ∫ t in a..b, ph a = ph a * (b - a) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      rw [← h1]
      apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
      intro t ht
      exact hLmono a t ha ht.1
    · have h1 : ∫ t in a..b, ph b = ph b * (b - a) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      rw [← h1]
      apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
      intro t ht
      exact hLmono t b (by linarith [ht.1]) ht.2
  have hLJ : ∫ t in (0:ℝ)..1, ph t = 2 * Real.log 2 - 1 := by
    have hG : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun s : ℝ => (1 + s) * Real.log (1 + s) - s) (ph t) t := by
      intro t ht
      have hne : (1 + t) ≠ 0 := ne_of_gt (by linarith)
      have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by
        simpa using (hasDerivAt_id t).const_add 1
      have h2 : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := h1.log hne
      have h3 := (h1.mul h2).sub (hasDerivAt_id t)
      have key : ph t = 1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1 := by
        rw [hph, mul_one_div_cancel hne]; ring
      rw [key]; exact h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => (1 + s) * Real.log (1 + s) - s) (f' := ph)]
    · norm_num
    · intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact hG t ht.1
    · exact hint 0 1 le_rfl zero_le_one zero_le_one le_rfl
  have hmain : ∀ x : ℝ, 0 < x → x < 1 →
      Real.exp (Real.log 2 - 1 - (1 - x)) ≤ xprod x ∧ xprod x ≤ Real.exp (Real.log 2 - 1) := by
    intro x hx0 hx1
    have hpow_nn : ∀ n : ℕ, 0 ≤ x ^ n := fun n => pow_nonneg hx0.le n
    have hpow_le : ∀ n : ℕ, x ^ n ≤ 1 := fun n => pow_le_one₀ hx0.le hx1.le
    have hab : ∀ m : ℕ, x ^ (m + 1) ≤ x ^ m := by
      intro m; rw [pow_succ]; nlinarith [hpow_nn m]
    have hph1 : ph (x ^ 0) = Real.log 2 := by
      rw [pow_zero, hph]; norm_num
    have hterm : ∀ n : ℕ, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (x ^ n * (ph (x ^ (n + 1)) - ph (x ^ n))) := by
      intro n
      have h1 : (0:ℝ) < 1 + x ^ (n + 1) := by linarith [hpow_nn (n + 1)]
      have h2 : (0:ℝ) < 1 + x ^ n := by linarith [hpow_nn n]
      rw [Real.rpow_def_of_pos (div_pos h1 h2), Real.log_div h1.ne' h2.ne', hph, hph]
      congr 1; ring
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ N, S N =
        ∑ n ∈ Finset.range N, x ^ n * (ph (x ^ (n + 1)) - ph (x ^ n)) :=
      ⟨fun N => ∑ n ∈ Finset.range N, x ^ n * (ph (x ^ (n + 1)) - ph (x ^ n)), fun N => rfl⟩
    have e : (fun N : ℕ => ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
        = fun N => Real.exp (S N) := by
      funext N
      rw [hS, Real.exp_sum]
      exact Finset.prod_congr rfl (fun n _ => hterm n)
    have hT : Tendsto (fun N : ℕ => Real.exp (S N)) atTop (𝓝 (xprod x)) := by
      have h := hxprod x ⟨hx0, hx1⟩
      rw [e] at h
      exact h
    have hT' : Tendsto (fun N : ℕ => Real.exp (S (N + 1))) atTop (𝓝 (xprod x)) :=
      (Filter.tendsto_add_atTop_iff_nat 1).mpr hT
    obtain ⟨W, hW⟩ : ∃ W : ℕ → ℝ, ∀ N, W N =
        ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * ph (x ^ (m + 1)) :=
      ⟨fun N => ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * ph (x ^ (m + 1)), fun N => rfl⟩
    have hid : ∀ N : ℕ, S (N + 1) = x ^ N * ph (x ^ (N + 1)) - ph (x ^ 0) + W N := by
      intro N
      induction N with
      | zero => simp [hS, hW]
      | succ k ih =>
        simp only [hS, hW, Finset.sum_range_succ] at ih ⊢
        linear_combination ih
    obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ N, F N = ∫ t in x ^ N..1, ph t :=
      ⟨fun N => ∫ t in x ^ N..1, ph t, fun N => rfl⟩
    have hFsum : ∀ N : ℕ, ∑ m ∈ Finset.range N, (∫ t in x ^ (m + 1)..x ^ m, ph t) = F N := by
      intro N
      induction N with
      | zero => simp [hF]
      | succ k ih =>
        rw [Finset.sum_range_succ, ih, hF, hF]
        have := intervalIntegral.integral_add_adjacent_intervals
          (hint _ _ (hpow_nn (k + 1)) (hpow_le (k + 1)) (hpow_nn k) (hpow_le k))
          (hint _ _ (hpow_nn k) (hpow_le k) zero_le_one le_rfl)
        linarith
    have hFb : ∀ N : ℕ, F N ≤ 2 * Real.log 2 - 1 ∧ 2 * Real.log 2 - 1 - x ^ N ≤ F N := by
      intro N
      have hs := intervalIntegral.integral_add_adjacent_intervals
        (hint 0 (x ^ N) le_rfl zero_le_one (hpow_nn N) (hpow_le N))
        (hint (x ^ N) 1 (hpow_nn N) (hpow_le N) zero_le_one le_rfl)
      rw [← hF N, hLJ] at hs
      obtain ⟨h1, h2⟩ := hLI 0 (x ^ N) le_rfl (hpow_nn N) (hpow_le N)
      rw [hL0, zero_mul] at h1
      have h3 : ph (x ^ N) * (x ^ N - 0) ≤ x ^ N := by
        nlinarith [hL2 (x ^ N) (hpow_nn N), hpow_nn N, hpow_le N]
      constructor <;> linarith
    have hWb : ∀ N : ℕ, F N - (1 - x) ≤ W N ∧ W N ≤ F N := by
      intro N
      have hE : ∀ N : ℕ, ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) = 1 - x ^ N := by
        intro N
        induction N with
        | zero => simp
        | succ k ih => rw [Finset.sum_range_succ, ih]; ring
      have hup : W N ≤ F N := by
        rw [← hFsum N, hW]
        apply Finset.sum_le_sum
        intro m _
        have := (hLI (x ^ (m + 1)) (x ^ m) (hpow_nn _) (hab m) (hpow_le m)).1
        linarith
      have hterm_b : ∀ m : ℕ, (∫ t in x ^ (m + 1)..x ^ m, ph t) - (1 - x) * (x ^ m - x ^ (m + 1))
          ≤ (x ^ m - x ^ (m + 1)) * ph (x ^ (m + 1)) := by
        intro m
        have hA := (hLI (x ^ (m + 1)) (x ^ m) (hpow_nn _) (hab m) (hpow_le m)).2
        have hB := hL1 (x ^ (m + 1)) (x ^ m) (hpow_nn _) (hab m)
        have hC : 0 ≤ x ^ m - x ^ (m + 1) := by linarith [hab m]
        have hD : x ^ m - x ^ (m + 1) ≤ 1 - x := by
          rw [pow_succ]
          nlinarith [mul_nonneg (sub_nonneg.2 (hpow_le m)) (sub_nonneg.2 hx1.le)]
        nlinarith [mul_le_mul_of_nonneg_left hB hC, mul_le_mul_of_nonneg_right hD hC]
      have hsum := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range N) => hterm_b m)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hE N, hFsum N, ← hW N] at hsum
      constructor
      · nlinarith [hsum, mul_nonneg (sub_nonneg.2 hx1.le) (hpow_nn N)]
      · exact hup
    have hSup : ∀ N : ℕ, Real.exp (S (N + 1)) ≤ Real.exp (Real.log 2 - 1 + x ^ N) := by
      intro N
      apply Real.exp_le_exp.2
      rw [hid N, hph1]
      have hA1 : x ^ N * ph (x ^ (N + 1)) ≤ x ^ N := by
        have h := hL2 (x ^ (N + 1)) (hpow_nn _)
        have h' := hpow_le (N + 1)
        nlinarith [mul_nonneg (hpow_nn N) (show (0:ℝ) ≤ 1 - ph (x ^ (N + 1)) by linarith)]
      linarith [hA1, (hWb N).2, (hFb N).1]
    have hSlow : ∀ N : ℕ, Real.exp (Real.log 2 - 1 - x ^ N - (1 - x)) ≤ Real.exp (S (N + 1)) := by
      intro N
      apply Real.exp_le_exp.2
      rw [hid N, hph1]
      have hA0 : 0 ≤ x ^ N * ph (x ^ (N + 1)) := mul_nonneg (hpow_nn N) (hLnn _ (hpow_nn _))
      linarith [(hWb N).1, (hFb N).2]
    have hc1 : Tendsto (fun N : ℕ => Real.log 2 - 1 + x ^ N) atTop (𝓝 (Real.log 2 - 1 + 0)) :=
      (tendsto_const_nhds).add (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1)
    rw [add_zero] at hc1
    have hlim1 := (Real.continuous_exp.tendsto (Real.log 2 - 1)).comp hc1
    have hc2 : Tendsto (fun N : ℕ => Real.log 2 - 1 - x ^ N - (1 - x)) atTop
        (𝓝 (Real.log 2 - 1 - 0 - (1 - x))) :=
      ((tendsto_const_nhds).sub (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1)).sub
        tendsto_const_nhds
    rw [sub_zero] at hc2
    have hlim2 := (Real.continuous_exp.tendsto (Real.log 2 - 1 - (1 - x))).comp hc2
    constructor
    · exact le_of_tendsto_of_tendsto' hlim2 hT' (fun N => hSlow N)
    · exact le_of_tendsto_of_tendsto' hT' hlim1 (fun N => hSup N)
  have hval : Real.exp (Real.log 2 - 1) = 2 / Real.exp 1 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  show Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  rw [← hval]
  have hcont : Continuous (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) := by fun_prop
  have hg : Tendsto (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) (𝓝[<] 1)
      (𝓝 (Real.exp (Real.log 2 - 1))) := by
    have h := hcont.tendsto 1
    simp only [sub_self, sub_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    exact (hmain x hx.1 hx.2).1
  · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
    exact (hmain x hx.1 hx.2).2
