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
  show Tendsto xprod (𝓝[<] 1) (𝓝 (2 / Real.exp 1))
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ, ∀ y, G y = (1 + y) * Real.log (1 + y) - y :=
    ⟨fun y => (1 + y) * Real.log (1 + y) - y, fun _ => rfl⟩
  have hGfun : G = fun y => (1 + y) * Real.log (1 + y) - y := funext hG
  have hderiv : ∀ y : ℝ, 0 ≤ y → HasDerivAt G (Real.log (1 + y)) y := by
    intro y hy
    have hne : (1 + y) ≠ 0 := ne_of_gt (by linarith)
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 y := by
      simpa using (hasDerivAt_id y).const_add 1
    have h2 : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + y)) y := h1.log hne
    have h3 := (h1.mul h2).sub (hasDerivAt_id y)
    rw [hGfun]
    refine h3.congr_deriv ?_
    field_simp
    ring
  have hGb : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (b - a) * Real.log (1 + a) ≤ G b - G a ∧ G b - G a ≤ (b - a) * Real.log (1 + b) := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h | h
    · subst h; simp
    · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope G (fun y => Real.log (1 + y)) h
        (fun y hy => (hderiv y (by linarith [hy.1])).continuousAt.continuousWithinAt)
        (fun y hy => hderiv y (by linarith [hy.1]))
      have hba : b - a ≠ 0 := ne_of_gt (by linarith)
      have hsl : G b - G a = Real.log (1 + c) * (b - a) := by
        rw [hceq]; field_simp
      have l1 : Real.log (1 + a) ≤ Real.log (1 + c) :=
        Real.log_le_log (by linarith) (by linarith [hc.1])
      have l2 : Real.log (1 + c) ≤ Real.log (1 + b) :=
        Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
      have hp : 0 ≤ b - a := by linarith
      constructor
      · rw [hsl]; nlinarith [mul_le_mul_of_nonneg_right l1 hp]
      · rw [hsl]; nlinarith [mul_le_mul_of_nonneg_right l2 hp]
  have hlogd : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      Real.log (1 + b) - Real.log (1 + a) ≤ b - a := by
    intro a b ha hab
    have hpos1 : (0:ℝ) < 1 + a := by linarith
    have hpos2 : (0:ℝ) < 1 + b := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos hpos2 hpos1)
    rw [Real.log_div hpos2.ne' hpos1.ne'] at h
    have h2 : (1 + b) / (1 + a) - 1 = (b - a) / (1 + a) := by
      rw [div_sub_one hpos1.ne']; congr 1; ring
    have h3 : (b - a) / (1 + a) ≤ b - a := div_le_self (by linarith) (by linarith)
    linarith
  have hprod : ∀ x : ℝ, 0 < x → ∀ N : ℕ,
      (∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)) =
        Real.exp (x ^ N * Real.log (1 + x ^ N) - Real.log 2 +
          ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * Real.log (1 + x ^ (m + 1))) := by
    intro x hx N
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty, pow_zero, one_mul,
        add_zero]
      norm_num
    | succ N ih =>
      have pA : 0 < 1 + x ^ (N + 1) := by have := pow_pos hx (N + 1); linarith
      have pB : 0 < 1 + x ^ N := by have := pow_pos hx N; linarith
      have hr : 0 < (1 + x ^ (N + 1)) / (1 + x ^ N) := div_pos pA pB
      rw [Finset.prod_range_succ, ih, Finset.sum_range_succ, Real.rpow_def_of_pos hr,
        ← Real.exp_add]
      congr 1
      rw [Real.log_div pA.ne' pB.ne']
      ring
  have hQ : ∀ x : ℝ, 0 < x → x < 1 → ∀ N : ℕ,
      G 1 - G (x ^ N) - (1 - x) * (1 - x ^ N) ≤
          ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * Real.log (1 + x ^ (m + 1)) ∧
      ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * Real.log (1 + x ^ (m + 1)) ≤
          G 1 - G (x ^ N) := by
    intro x hx0 hx1 N
    induction N with
    | zero => simp
    | succ N ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hxN1 : x ^ (N + 1) ≤ x ^ N := by
        rw [pow_succ]; nlinarith [pow_nonneg hx0.le N]
      have hxN : x ^ N ≤ 1 := pow_le_one₀ hx0.le hx1.le
      have hpN : 0 ≤ x ^ N := pow_nonneg hx0.le N
      have hpN1 : 0 ≤ x ^ (N + 1) := pow_nonneg hx0.le _
      obtain ⟨t1, t2⟩ := hGb (x ^ (N + 1)) (x ^ N) hpN1 hxN1
      have hd1 := hlogd (x ^ (N + 1)) (x ^ N) hpN1 hxN1
      have hw0 : 0 ≤ x ^ N - x ^ (N + 1) := by linarith
      have hw1 : x ^ N - x ^ (N + 1) ≤ 1 - x := by
        have : x ^ (N + 1) = x ^ N * x := pow_succ x N
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_right hxN (by linarith : (0:ℝ) ≤ 1 - x)]
      have key1 : (x ^ N - x ^ (N + 1)) * Real.log (1 + x ^ (N + 1))
          ≥ G (x ^ N) - G (x ^ (N + 1)) - (1 - x) * (x ^ N - x ^ (N + 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hd1 hw0, mul_le_mul_of_nonneg_right hw1 hw0]
      have e : (1 - x) * (1 - x ^ (N + 1)) = (1 - x) * (1 - x ^ N) + (1 - x) * (x ^ N - x ^ (N + 1)) := by ring
      rw [Finset.sum_range_succ]
      constructor
      · linarith [key1, ih1, e]
      · linarith [t1, ih2]
  have hG1 : G 1 = 2 * Real.log 2 - 1 := by rw [hG]; norm_num
  have hexp : Real.exp (Real.log 2 - 1) = 2 / Real.exp 1 := by
    rw [Real.exp_sub, Real.exp_log two_pos]
  have hbound : ∀ x ∈ Set.Ioo (0:ℝ) 1,
      Real.exp (Real.log 2 - 1 - (1 - x)) ≤ xprod x ∧ xprod x ≤ Real.exp (Real.log 2 - 1) := by
    rintro x ⟨hx0, hx1⟩
    have hlim := hxprod x ⟨hx0, hx1⟩
    simp only [hprod x hx0] at hlim
    have hxN : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hlog0 : Tendsto (fun y : ℝ => Real.log (1 + y)) (𝓝 0) (𝓝 0) := by
      have h : Tendsto (fun y : ℝ => 1 + y) (𝓝 0) (𝓝 1) := by
        exact (continuous_const.add continuous_id : Continuous fun y : ℝ => (1:ℝ) + y).tendsto' (0:ℝ) 1 (by norm_num)
      have h2 := h.log one_ne_zero
      simpa using h2
    have hd : Tendsto (fun N : ℕ => x ^ N - Real.log (1 + x ^ N)) atTop (𝓝 0) := by
      have := hxN.sub (hlog0.comp hxN)
      simpa using this
    have hU : Tendsto (fun N : ℕ => Real.exp (Real.log 2 - 1 + (x ^ N - Real.log (1 + x ^ N))))
        atTop (𝓝 (Real.exp (Real.log 2 - 1 + 0))) :=
      (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.add hd)
    have hL : Tendsto (fun N : ℕ => Real.exp (Real.log 2 - 1 - (1 - x) + (x ^ N - Real.log (1 + x ^ N))))
        atTop (𝓝 (Real.exp (Real.log 2 - 1 - (1 - x) + 0))) :=
      (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.add hd)
    rw [add_zero] at hU hL
    have hsand : ∀ N : ℕ, Real.exp (Real.log 2 - 1 - (1 - x) + (x ^ N - Real.log (1 + x ^ N)))
        ≤ Real.exp (x ^ N * Real.log (1 + x ^ N) - Real.log 2 +
          ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * Real.log (1 + x ^ (m + 1))) ∧
        Real.exp (x ^ N * Real.log (1 + x ^ N) - Real.log 2 +
          ∑ m ∈ Finset.range N, (x ^ m - x ^ (m + 1)) * Real.log (1 + x ^ (m + 1)))
          ≤ Real.exp (Real.log 2 - 1 + (x ^ N - Real.log (1 + x ^ N))) := by
      intro N
      obtain ⟨q1, q2⟩ := hQ x hx0 hx1 N
      rw [hG1, hG (x ^ N)] at q1 q2
      have e : (1 + x ^ N) * Real.log (1 + x ^ N) = Real.log (1 + x ^ N) + x ^ N * Real.log (1 + x ^ N) := by ring
      have hm : (1 - x) * (1 - x ^ N) ≤ 1 - x := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) (pow_nonneg hx0.le N)]
      constructor
      · apply Real.exp_le_exp.2
        linarith
      · apply Real.exp_le_exp.2
        linarith
    have hlo' := le_of_tendsto_of_tendsto' hL hlim (fun N => (hsand N).1)
    have hhi' := le_of_tendsto_of_tendsto' hlim hU (fun N => (hsand N).2)
    exact ⟨hlo', hhi'⟩
  have hlo : Tendsto (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) (𝓝[<] 1)
      (𝓝 (2 / Real.exp 1)) := by
    have hc : Continuous (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) := by fun_prop
    have : Tendsto (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x))) (𝓝[<] 1)
        (𝓝 (Real.exp (Real.log 2 - 1 - (1 - 1)))) := (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    rw [show (Real.log 2 - 1 - (1 - 1 : ℝ)) = Real.log 2 - 1 by ring, hexp] at this
    exact this
  have hhi : Tendsto (fun _ : ℝ => Real.exp (Real.log 2 - 1)) (𝓝[<] 1) (𝓝 (2 / Real.exp 1)) := by
    rw [← hexp]; exact tendsto_const_nhds
  have hev : ∀ᶠ x in 𝓝[<] (1:ℝ), x ∈ Set.Ioo (0:ℝ) 1 :=
    Filter.eventually_of_mem (Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)) (fun x hx => hx)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hev.mono fun x hx => (hbound x hx).1) (hev.mono fun x hx => (hbound x hx).2)
