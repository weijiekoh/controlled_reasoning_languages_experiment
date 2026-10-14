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
  have hFd : ∀ t : ℝ, -1 < t → HasDerivAt F (Real.log (1 + t)) t := by
    intro t ht
    have hne : (1 + t) ≠ 0 := (by linarith : (0:ℝ) < 1 + t).ne'
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := by
      simpa using (hasDerivAt_id t).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + t)) t := h1.log hne
    have h3 : HasDerivAt (fun y : ℝ => (1 + y) * Real.log (1 + y) - y)
        (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1) t :=
      (h1.mul h2).sub (hasDerivAt_id t)
    have h4 : (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t)) - 1) = Real.log (1 + t) := by
      rw [one_mul, mul_one_div, div_self hne]; ring
    rw [h4] at h3
    have hfun : F = fun y : ℝ => (1 + y) * Real.log (1 + y) - y := by
      funext y; exact hF y
    rw [hfun]; exact h3
  have hF0 : F 0 = 0 := by rw [hF 0]; simp
  have hF1 : F 1 = 2 * Real.log 2 - 1 := by rw [hF 1]; norm_num
  have hS : ∀ a b : ℝ, 0 ≤ a → a < b →
      (b - a) * Real.log (1 + a) ≤ F b - F a ∧ F b - F a ≤ (b - a) * Real.log (1 + b) := by
    intro a b ha hab
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope F (fun t => Real.log (1 + t)) hab
      (fun t ht => (hFd t (by linarith [ht.1])).continuousAt.continuousWithinAt)
      (fun t ht => hFd t (by linarith [ht.1]))
    have hceq' : Real.log (1 + c) = (F b - F a) / (b - a) := hceq
    have hne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hc' : F b - F a = Real.log (1 + c) * (b - a) := by
      rw [hceq', div_mul_cancel₀ _ hne]
    have hm1 : Real.log (1 + a) ≤ Real.log (1 + c) :=
      Real.log_le_log (by linarith) (by linarith [hc.1])
    have hm2 : Real.log (1 + c) ≤ Real.log (1 + b) :=
      Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
    have hba : 0 ≤ b - a := by linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hm1 hba]
    · nlinarith [mul_le_mul_of_nonneg_right hm2 hba]
  have key : ∀ x : ℝ, 0 < x → x < 1 → ∃ Q : ℝ, F 1 ≤ Q ∧ Q ≤ F 1 + (1 - x) ∧
      xprod x = Real.exp ((Q - Real.log 2) / x) := by
    intro x hx0 hx1
    have hxN : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hA : ∀ n : ℕ, 0 < 1 + x ^ n := fun n => by
      have := pow_nonneg hx0.le n; linarith
    have hFc : Tendsto F (𝓝 0) (𝓝 0) := by
      have := (hFd 0 (by norm_num)).continuousAt.tendsto
      rwa [hF0] at this
    have hFN : Tendsto (fun N : ℕ => F (x ^ N)) atTop (𝓝 0) := hFc.comp hxN
    have hG : Tendsto (fun N : ℕ => F 1 - F (x ^ N)) atTop (𝓝 (F 1)) := by
      have := (tendsto_const_nhds (x := F 1)).sub hFN
      simpa using this
    have hFnn : ∀ N : ℕ, 0 ≤ F (x ^ N) := by
      intro N
      have h := (hS 0 (x ^ N) le_rfl (pow_pos hx0 N)).1
      simp only [add_zero, Real.log_one, mul_zero, hF0, sub_zero] at h
      linarith
    have hxa : ∀ N : ℕ, x ^ (N + 1) = x * x ^ N := fun N => by rw [pow_succ]; ring
    have hinv : ∀ N : ℕ,
        F 1 - F (x ^ N) ≤ (1 - x) * ∑ m ∈ Finset.range N, x ^ m * Real.log (1 + x ^ m) ∧
        (1 - x) * ∑ m ∈ Finset.range N, x ^ m * Real.log (1 + x ^ m)
          ≤ F 1 - F (x ^ N) + (1 - x) * (1 - x ^ N) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hb0 : 0 ≤ x ^ N := pow_nonneg hx0.le N
        have hb1 : x ^ N ≤ 1 := pow_le_one₀ hx0.le hx1.le
        have hbpos : 0 < x ^ N := pow_pos hx0 N
        have hab : x * x ^ N < x ^ N := by nlinarith [mul_pos hbpos (sub_pos.2 hx1)]
        have hS' := hS (x * x ^ N) (x ^ N) (mul_nonneg hx0.le hb0) hab
        have hpos : 0 < 1 + x * x ^ N := by linarith [mul_nonneg hx0.le hb0]
        have D1 : Real.log (1 + x ^ N) - Real.log (1 + x * x ^ N) ≤ (1 - x) * x ^ N := by
          rw [← Real.log_div (hA N).ne' hpos.ne']
          have h1 := Real.log_le_sub_one_of_pos (div_pos (hA N) hpos)
          have h2 : (1 + x ^ N) / (1 + x * x ^ N) ≤ 1 + (1 - x) * x ^ N := by
            rw [div_le_iff₀ hpos]
            nlinarith [mul_nonneg (mul_nonneg hx0.le (sub_nonneg.2 hx1.le)) (mul_nonneg hb0 hb0)]
          linarith
        have hnn : 0 ≤ (1 - x) * x ^ N := mul_nonneg (sub_nonneg.2 hx1.le) hb0
        have hm1 := mul_le_mul_of_nonneg_left D1 hnn
        have hm2 : 0 ≤ (1 - x) ^ 2 * x ^ N * (1 - x ^ N) :=
          mul_nonneg (mul_nonneg (sq_nonneg _) hb0) (sub_nonneg.2 hb1)
        rw [Finset.sum_range_succ, hxa]
        constructor
        · nlinarith [hS'.2, ih1]
        · nlinarith [hS'.1, hm1, hm2, ih2]
    have hmono : Monotone (fun N : ℕ => (1 - x) * ∑ m ∈ Finset.range N, x ^ m * Real.log (1 + x ^ m)) := by
      apply monotone_nat_of_le_succ
      intro n
      rw [Finset.sum_range_succ]
      have h0 : 0 ≤ x ^ n * Real.log (1 + x ^ n) :=
        mul_nonneg (pow_nonneg hx0.le n) (Real.log_nonneg (by linarith [pow_nonneg hx0.le n]))
      nlinarith [mul_nonneg (sub_nonneg.2 hx1.le) h0]
    have hbdd : BddAbove (Set.range (fun N : ℕ => (1 - x) * ∑ m ∈ Finset.range N, x ^ m * Real.log (1 + x ^ m))) := by
      refine ⟨F 1 + (1 - x), ?_⟩
      rintro _ ⟨N, rfl⟩
      dsimp only
      have h1 := (hinv N).2
      have h2 := hFnn N
      have h3 : 0 ≤ (1 - x) * x ^ N := mul_nonneg (sub_nonneg.2 hx1.le) (pow_nonneg hx0.le N)
      nlinarith
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Tendsto (fun N : ℕ => (1 - x) * ∑ m ∈ Finset.range N, x ^ m * Real.log (1 + x ^ m)) atTop (𝓝 Q) :=
      ⟨_, tendsto_atTop_ciSup hmono hbdd⟩
    have hQlo : F 1 ≤ Q :=
      le_of_tendsto_of_tendsto' hG hQ (fun N => (hinv N).1)
    have hG2 : Tendsto (fun N : ℕ => F 1 - F (x ^ N) + (1 - x) * (1 - x ^ N)) atTop (𝓝 (F 1 + (1 - x))) := by
      have := hG.add (((tendsto_const_nhds (x := (1:ℝ))).sub hxN).const_mul (1 - x))
      simpa using this
    have hQhi : Q ≤ F 1 + (1 - x) :=
      le_of_tendsto_of_tendsto' hQ hG2 (fun N => (hinv N).2)
    have hT2 : Tendsto (fun N : ℕ => x ^ N * Real.log (1 + x ^ N)) atTop (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => t * Real.log (1 + t)) 0 := by
        apply ContinuousAt.mul continuousAt_id
        apply ContinuousAt.log (by fun_prop) (by norm_num)
      have h2 : Tendsto (fun N : ℕ => x ^ N * Real.log (1 + x ^ N)) atTop (𝓝 (0 * Real.log (1 + 0))) :=
        hc.tendsto.comp hxN
      simpa using h2
    have hLid : ∀ N : ℕ, x * ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))
        = (1 - x) * ∑ m ∈ Finset.range N, x ^ m * Real.log (1 + x ^ m) + x ^ N * Real.log (1 + x ^ N) - Real.log 2 := by
      intro N
      induction N with
      | zero => norm_num
      | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linear_combination ih
    have hprod : ∀ N : ℕ, ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) := by
      intro N
      have hposP : 0 < ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n) :=
        Finset.prod_pos (fun n _ => Real.rpow_pos_of_pos (div_pos (hA (n + 1)) (hA n)) _)
      rw [← Real.exp_log hposP]
      congr 1
      rw [Real.log_prod (fun n _ => (Real.rpow_pos_of_pos (div_pos (hA (n + 1)) (hA n)) _).ne')]
      apply Finset.sum_congr rfl
      intro n _
      rw [Real.log_rpow (div_pos (hA (n + 1)) (hA n)), Real.log_div (hA (n + 1)).ne' (hA n).ne']
    have hE : Tendsto (fun N : ℕ => Real.exp (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)))) atTop (𝓝 (xprod x)) :=
      (hxprod x ⟨hx0, hx1⟩).congr hprod
    have hxL : Tendsto (fun N : ℕ => x * ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) atTop (𝓝 (Q - Real.log 2)) := by
      have h := (hQ.add hT2).sub_const (Real.log 2)
      rw [add_zero] at h
      exact h.congr (fun N => (hLid N).symm)
    have hLt : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n))) atTop (𝓝 ((Q - Real.log 2) / x)) :=
      (hxL.div_const x).congr (fun N => mul_div_cancel_left₀ _ hx0.ne')
    have hX : Tendsto (fun N : ℕ => Real.exp (∑ n ∈ Finset.range N, x ^ n * (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)))) atTop (𝓝 (Real.exp ((Q - Real.log 2) / x))) :=
      (Real.continuous_exp.tendsto _).comp hLt
    refine ⟨Q, hQlo, hQhi, ?_⟩
    exact tendsto_nhds_unique hE hX
  choose! Q hQ using key
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlim : Tendsto Q (𝓝[<] 1) (𝓝 (F 1)) := by
    have hu : Tendsto (fun x : ℝ => F 1 + (1 - x)) (𝓝[<] 1) (𝓝 (F 1)) := by
      have hc : Continuous (fun x : ℝ => F 1 + (1 - x)) := by fun_prop
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
      exact (hQ x hx.1 hx.2).1
    · filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
      exact (hQ x hx.1 hx.2).2.1
  have h1 : Tendsto (fun x : ℝ => (Q x - Real.log 2) / x) (𝓝[<] 1) (𝓝 ((F 1 - Real.log 2) / 1)) :=
    (hlim.sub_const (Real.log 2)).div hid one_ne_zero
  have hfinal := (Real.continuous_exp.tendsto _).comp h1
  have hval : Real.exp ((F 1 - Real.log 2) / 1) = 2 / Real.exp 1 := by
    rw [hF1, div_one, show 2 * Real.log 2 - 1 - Real.log 2 = Real.log 2 - 1 by ring,
      Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  show Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  rw [← hval]
  refine Tendsto.congr' ?_ hfinal
  filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with x hx
  exact (hQ x hx.1 hx.2).2.2.symm
