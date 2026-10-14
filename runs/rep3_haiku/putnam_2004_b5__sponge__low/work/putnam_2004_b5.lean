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
  have hderiv : ∀ u : ℝ, 0 < 1 + u →
      HasDerivAt (fun u : ℝ => (1 + u) * Real.log (1 + u) - u) (Real.log (1 + u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 u := by
      simpa using (hasDerivAt_id' u).const_add 1
    have h2 : HasDerivAt (fun u : ℝ => Real.log (1 + u)) (1 / (1 + u)) u :=
      h1.log (ne_of_gt hu)
    have h3 := (h1.mul h2).sub (hasDerivAt_id' u)
    refine HasDerivAt.congr_deriv h3 ?_
    rw [mul_one_div_cancel (ne_of_gt hu)]
    ring
  have hmvt : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Real.log (1 + a) * (b - a) ≤ ((1 + b) * Real.log (1 + b) - b) - ((1 + a) * Real.log (1 + a) - a) ∧
      ((1 + b) * Real.log (1 + b) - b) - ((1 + a) * Real.log (1 + a) - a) ≤ Real.log (1 + b) * (b - a) := by
    intro a b ha hab hb
    rcases eq_or_lt_of_le hab with h | h
    · subst h; simp
    · obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope
        (fun u : ℝ => (1 + u) * Real.log (1 + u) - u) (fun u : ℝ => Real.log (1 + u)) h
        (fun u hu => (hderiv u (by linarith [hu.1])).continuousAt.continuousWithinAt)
        (fun u hu => hderiv u (by linarith [hu.1]))
      have hpos : 0 < b - a := by linarith
      have hFc : ((1 + b) * Real.log (1 + b) - b) - ((1 + a) * Real.log (1 + a) - a)
          = Real.log (1 + c) * (b - a) := by
        rw [hceq, div_mul_cancel₀ _ hpos.ne']
      have m1 : Real.log (1 + a) ≤ Real.log (1 + c) :=
        Real.log_le_log (by linarith) (by linarith [hc.1])
      have m2 : Real.log (1 + c) ≤ Real.log (1 + b) :=
        Real.log_le_log (by linarith [hc.1]) (by linarith [hc.2])
      rw [hFc]
      exact ⟨mul_le_mul_of_nonneg_right m1 hpos.le, mul_le_mul_of_nonneg_right m2 hpos.le⟩
  -- main per-x estimate
  have key : ∀ x : ℝ, 0 < x → x < 1 → ∃ c : ℝ,
      xprod x = Real.exp (-Real.log 2 + c) ∧
      (2 * Real.log 2 - 1) - (1 - x) * Real.log 2 ≤ c ∧ c ≤ 2 * Real.log 2 - 1 := by
    intro x hx0 hx1
    have hF1 : (1 + 1 : ℝ) * Real.log (1 + 1) - 1 = 2 * Real.log 2 - 1 := by
      rw [show (1 : ℝ) + 1 = 2 by norm_num]
    have hxn : ∀ N : ℕ, 0 < x ^ N := fun N => pow_pos hx0 N
    have hxle : ∀ N : ℕ, x ^ N ≤ 1 := fun N => pow_le_one₀ hx0.le hx1.le
    obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, ∀ N, A N =
        ∑ n ∈ Finset.range N, (x ^ n - x ^ (n + 1)) * Real.log (1 + x ^ (n + 1)) :=
      ⟨_, fun N => rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : ℕ → ℝ, ∀ N, S N =
        ∑ n ∈ Finset.range N, (Real.log (1 + x ^ (n + 1)) - Real.log (1 + x ^ n)) * x ^ n :=
      ⟨_, fun N => rfl⟩
    have hP : ∀ N, ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (S N) := by
      intro N
      rw [hS, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro n _
      have hpa : 0 < 1 + x ^ n := by linarith [hxn n]
      have hpb : 0 < 1 + x ^ (n + 1) := by linarith [hxn (n + 1)]
      rw [Real.rpow_def_of_pos (div_pos hpb hpa), Real.log_div hpb.ne' hpa.ne']
    have hid : ∀ N, S N = -Real.log 2 + A N + x ^ N * Real.log (1 + x ^ N) := by
      intro N
      induction N with
      | zero => norm_num [hS, hA]
      | succ N ih =>
        have e1 : S (N + 1) = S N + (Real.log (1 + x ^ (N + 1)) - Real.log (1 + x ^ N)) * x ^ N := by
          rw [hS, hS, Finset.sum_range_succ]
        have e2 : A (N + 1) = A N + (x ^ N - x ^ (N + 1)) * Real.log (1 + x ^ (N + 1)) := by
          rw [hA, hA, Finset.sum_range_succ]
        rw [e1, e2, ih]; ring
    have hgnn : ∀ N : ℕ, 0 ≤ Real.log (1 + x ^ N) := fun N =>
      Real.log_nonneg (by linarith [hxn N])
    have hgle : ∀ N : ℕ, Real.log (1 + x ^ (N + 1)) ≤ Real.log (1 + x ^ N) := fun N =>
      Real.log_le_log (by linarith [hxn (N + 1)])
        (by have : x ^ (N + 1) ≤ x ^ N := pow_le_pow_of_le_one hx0.le hx1.le (Nat.le_succ N)
            linarith)
    have hdnn : ∀ N : ℕ, 0 ≤ x ^ N - x ^ (N + 1) := by
      intro N; rw [pow_succ]; nlinarith [hxn N]
    have hd : ∀ N : ℕ, x ^ N - x ^ (N + 1) ≤ 1 - x := by
      intro N; rw [pow_succ]
      nlinarith [mul_nonneg (sub_nonneg.2 (hxle N)) (sub_nonneg.2 hx1.le)]
    -- upper bound
    have hU : ∀ N : ℕ, A N ≤ ((1 + 1) * Real.log (1 + 1) - 1) - ((1 + x ^ N) * Real.log (1 + x ^ N) - x ^ N) := by
      intro N
      induction N with
      | zero => norm_num [hA]
      | succ N ih =>
        have h1 := (hmvt (x ^ (N + 1)) (x ^ N) (hxn (N + 1)).le
          (pow_le_pow_of_le_one hx0.le hx1.le (Nat.le_succ N)) (hxle N)).1
        rw [hA (N + 1), Finset.sum_range_succ, ← hA N]
        nlinarith [h1, ih]
    -- lower bound
    have hL : ∀ N : ℕ, ((1 + 1) * Real.log (1 + 1) - 1) - ((1 + x ^ N) * Real.log (1 + x ^ N) - x ^ N)
        - (1 - x) * (Real.log 2 - Real.log (1 + x ^ N)) ≤ A N := by
      intro N
      induction N with
      | zero => norm_num [hA]
      | succ N ih =>
        have h2 := (hmvt (x ^ (N + 1)) (x ^ N) (hxn (N + 1)).le
          (pow_le_pow_of_le_one hx0.le hx1.le (Nat.le_succ N)) (hxle N)).2
        rw [hA (N + 1), Finset.sum_range_succ, ← hA N]
        nlinarith [h2, ih, mul_nonneg (sub_nonneg.2 (hd N)) (sub_nonneg.2 (hgle N))]
    -- F nonnegative
    have hFnn : ∀ N : ℕ, 0 ≤ (1 + x ^ N) * Real.log (1 + x ^ N) - x ^ N := by
      intro N
      have h := (hmvt 0 (x ^ N) le_rfl (hxn N).le (hxle N)).1
      have hl0 : Real.log (1 + 0) = 0 := by norm_num
      have hF0 : (1 + 0 : ℝ) * Real.log (1 + 0) - 0 = 0 := by norm_num
      rw [hF0, hl0, zero_mul] at h
      linarith
    have hFb : ∀ N : ℕ, (1 + x ^ N) * Real.log (1 + x ^ N) - x ^ N ≤ x ^ N * Real.log 2 := by
      intro N
      have h := (hmvt 0 (x ^ N) le_rfl (hxn N).le (hxle N)).2
      have hl0 : Real.log (1 + 0) = 0 := by norm_num
      have hF0 : (1 + 0 : ℝ) * Real.log (1 + 0) - 0 = 0 := by norm_num
      have hl2 : Real.log (1 + x ^ N) ≤ Real.log 2 :=
        Real.log_le_log (by linarith [hxn N]) (by linarith [hxle N])
      rw [hF0, sub_zero] at h
      nlinarith [hxn N]
    have hgb : ∀ N : ℕ, Real.log (1 + x ^ N) ≤ Real.log 2 := fun N =>
      Real.log_le_log (by linarith [hxn N]) (by linarith [hxle N])
    have hlim0 : Tendsto (fun N : ℕ => x ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
    have hup : Tendsto (fun N : ℕ => x ^ N * Real.log 2) atTop (𝓝 0) := by
      simpa using hlim0.mul_const (Real.log 2)
    have hFlim : Tendsto (fun N : ℕ => (1 + x ^ N) * Real.log (1 + x ^ N) - x ^ N) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun N => hFnn N) (fun N => hFb N)
    have hglim : Tendsto (fun N : ℕ => Real.log (1 + x ^ N)) atTop (𝓝 0) := by
      have hg2 : Tendsto (fun N : ℕ => x ^ N * Real.log 2) atTop (𝓝 0) := hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hlim0 (fun N => hgnn N) (fun N => ?_)
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + x ^ N by linarith [hxn N])
      linarith
    have hmono : Monotone A := by
      apply monotone_nat_of_le_succ
      intro N
      rw [hA (N + 1), Finset.sum_range_succ, ← hA N]
      have := mul_nonneg (hdnn N) (hgnn (N + 1))
      linarith
    have hbdd : BddAbove (Set.range A) := by
      refine ⟨((1 + 1) * Real.log (1 + 1) - 1), ?_⟩
      rintro _ ⟨N, rfl⟩
      have := hU N
      linarith [hFnn N]
    obtain ⟨c, hc⟩ : ∃ c, Tendsto A atTop (𝓝 c) := ⟨_, tendsto_atTop_ciSup hmono hbdd⟩
    have hcle : c ≤ (2 * Real.log 2 - 1) := by
      rw [← hF1]
      exact le_of_tendsto' hc (fun N => by linarith [hU N, hFnn N])
    have hcge : (2 * Real.log 2 - 1) - (1 - x) * Real.log 2 ≤ c := by
      have hlow : Tendsto (fun N : ℕ => ((1 + 1) * Real.log (1 + 1) - 1)
          - ((1 + x ^ N) * Real.log (1 + x ^ N) - x ^ N)
          - (1 - x) * (Real.log 2 - Real.log (1 + x ^ N))) atTop
          (𝓝 (((1 + 1) * Real.log (1 + 1) - 1) - 0 - (1 - x) * (Real.log 2 - 0))) :=
        ((tendsto_const_nhds.sub hFlim).sub ((tendsto_const_nhds.sub hglim).const_mul _))
      have := le_of_tendsto_of_tendsto' hlow hc (fun N => hL N)
      rw [hF1] at this
      linarith
    have hSlim : Tendsto S atTop (𝓝 (-Real.log 2 + c + 0)) := by
      have hg : Tendsto (fun N : ℕ => x ^ N * Real.log (1 + x ^ N)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
          (fun N => mul_nonneg (hxn N).le (hgnn N)) (fun N => ?_)
        exact mul_le_mul_of_nonneg_left (hgb N) (hxn N).le
      have h1 : Tendsto (fun N : ℕ => -Real.log 2 + A N + x ^ N * Real.log (1 + x ^ N)) atTop
          (𝓝 (-Real.log 2 + c + 0)) := ((tendsto_const_nhds.add hc).add hg).congr' (by
            exact Filter.Eventually.of_forall (fun N => rfl))
      exact Tendsto.congr (fun N => (hid N).symm) h1
    have hPlim := ((Real.continuous_exp.tendsto _).comp hSlim).congr (fun N => (hP N).symm)
    refine ⟨c, ?_, hcge, hcle⟩
    rw [tendsto_nhds_unique (hxprod x ⟨hx0, hx1⟩) hPlim, add_zero]
  -- limit as x → 1⁻
  have hcont : Continuous (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x) * Real.log 2)) := by
    fun_prop
  have hlow : Tendsto (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x) * Real.log 2))
      (𝓝[<] 1) (𝓝 (Real.exp (Real.log 2 - 1))) := by
    have := tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Iio 1) (hcont.tendsto 1)
    simpa using this
  have hval : putnam_2004_b5_solution = Real.exp (Real.log 2 - 1) := by
    unfold putnam_2004_b5_solution
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2)]
  rw [hval]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with x hx
    obtain ⟨c, hxc, h1, h2⟩ := key x hx.1 hx.2
    rw [hxc]
    apply Real.exp_le_exp.mpr
    linarith
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with x hx
    obtain ⟨c, hxc, h1, h2⟩ := key x hx.1 hx.2
    rw [hxc]
    apply Real.exp_le_exp.mpr
    linarith
