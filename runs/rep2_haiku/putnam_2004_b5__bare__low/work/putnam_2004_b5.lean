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
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => Real.log (1 + t) := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, G = fun t => (1 + t) * Real.log (1 + t) - t := ⟨_, rfl⟩
  have gnn : ∀ t, 0 ≤ t → 0 ≤ g t := by
    intro t ht; rw [hg]; exact Real.log_nonneg (by linarith)
  have gle : ∀ t, 0 ≤ t → g t ≤ t := by
    intro t ht; rw [hg]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + t by linarith)
    simp only; linarith
  have gmono : ∀ p q, 0 ≤ p → p ≤ q → g p ≤ g q := by
    intro p q hp hpq; rw [hg]
    exact Real.log_le_log (by linarith) (by linarith)
  have g1 : g 1 = Real.log 2 := by rw [hg]; norm_num
  have G0 : G 0 = 0 := by rw [hGdef]; simp
  have G1 : G 1 = 2 * Real.log 2 - 1 := by rw [hGdef]; norm_num
  have hGd : ∀ t, -1 < t → HasDerivAt G (g t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := by
      simpa using (hasDerivAt_id t).const_add 1
    have h2 := h1.log (by linarith : (0:ℝ) < 1 + t).ne'
    have h3 := (h1.mul h2).sub (hasDerivAt_id t)
    rw [hGdef, hg]
    refine h3.congr_deriv ?_
    have : (1 + t) ≠ 0 := (by linarith : (0:ℝ) < 1 + t).ne'
    simp only [id]
    field_simp
    ring
  have Gdiff : ∀ p q, 0 ≤ p → p ≤ q →
      (q - p) * g p ≤ G q - G p ∧ G q - G p ≤ (q - p) * g q := by
    intro p q hp hpq
    rcases eq_or_lt_of_le hpq with h | h
    · subst h; simp
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope G g h
        (fun t ht => (hGd t (by linarith [ht.1])).continuousAt.continuousWithinAt)
        (fun t ht => hGd t (by linarith [ht.1]))
      have hq : G q - G p = g c * (q - p) := by
        rw [hcd]; field_simp [sub_ne_zero.2 h.ne']
      have h1 := gmono p c hp hc.1.le
      have h2 := gmono c q (by linarith [hc.1]) hc.2.le
      have h3 := mul_le_mul_of_nonneg_right h1 (sub_nonneg.2 hpq)
      have h4 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hpq)
      constructor <;> nlinarith
  have P1 : ∀ x : ℝ, 0 < x → x < 1 → ∀ N : ℕ,
      ∏ n ∈ Finset.range N, ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n)
        = Real.exp (∑ n ∈ Finset.range N, x ^ n * (g (x ^ (n + 1)) - g (x ^ n))) := by
    intro x hx0 hx1 N
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl (fun n _ => ?_)
    have hp1 : (0:ℝ) < 1 + x ^ (n+1) := by positivity
    have hp2 : (0:ℝ) < 1 + x ^ n := by positivity
    rw [Real.rpow_def_of_pos (div_pos hp1 hp2), Real.log_div hp1.ne' hp2.ne', hg]
    congr 1
    simp only
    ring
  have SBP : ∀ x : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range (N+1), x ^ n * (g (x ^ (n + 1)) - g (x ^ n))
      = x ^ N * g (x ^ (N+1)) - g 1 + ∑ m ∈ Finset.range N, (x ^ m - x ^ (m+1)) * g (x ^ (m+1)) := by
    intro x N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun m => (x ^ m - x ^ (m+1)) * g (x ^ (m+1)))]
      ring
  have main : ∀ x ∈ Set.Ioo (0:ℝ) 1, xprod x ∈ Set.Icc
      (Real.exp (Real.log 2 - 1 - (1 - x) * Real.log 2)) (Real.exp (Real.log 2 - 1)) := by
    rintro x ⟨hx0, hx1⟩
    obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun m => (x ^ m - x ^ (m+1)) * g (x ^ (m+1)) := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, c = fun m => (x ^ m - x ^ (m+1)) * g (x ^ m) := ⟨_, rfl⟩
    have ha' : ∀ m, a m = (x ^ m - x ^ (m+1)) * g (x ^ (m+1)) := fun m => by rw [ha]
    have hc' : ∀ m, c m = (x ^ m - x ^ (m+1)) * g (x ^ m) := fun m => by rw [hc]
    have hpow : ∀ m : ℕ, x ^ (m+1) = x ^ m * x := fun m => pow_succ x m
    have hxm0 : ∀ m : ℕ, 0 ≤ x ^ m := fun m => pow_nonneg hx0.le m
    have hxm1 : ∀ m : ℕ, x ^ m ≤ 1 := fun m => pow_le_one₀ hx0.le hx1.le
    have hxs : ∀ m : ℕ, x ^ (m+1) ≤ x ^ m := fun m => by
      rw [hpow]; nlinarith [hxm0 m]
    have hterm : ∀ m : ℕ, a m ≤ G (x^m) - G (x^(m+1)) ∧ G (x^m) - G (x^(m+1)) ≤ c m ∧
        c m - a m ≤ (1 - x) * (g (x^m) - g (x^(m+1))) := by
      intro m
      have hd := Gdiff (x^(m+1)) (x^m) (pow_nonneg hx0.le _) (hxs m)
      rw [ha' m, hc' m]
      have hgd : 0 ≤ g (x^m) - g (x^(m+1)) := by
        linarith [gmono (x^(m+1)) (x^m) (pow_nonneg hx0.le _) (hxs m)]
      have hgap : x^m - x^(m+1) ≤ 1 - x := by
        rw [hpow]; nlinarith [hxm1 m, hxm0 m]
      refine ⟨?_, ?_, ?_⟩
      · linarith [hd.1]
      · linarith [hd.2]
      · have := mul_le_mul_of_nonneg_right hgap hgd
        nlinarith
    have hgap0 : ∀ m : ℕ, 0 ≤ x^m - x^(m+1) := fun m => by linarith [hxs m]
    have ha_nn : ∀ m, 0 ≤ a m := fun m => by
      rw [ha' m]; exact mul_nonneg (hgap0 m) (gnn _ (pow_nonneg hx0.le _))
    have hc_nn : ∀ m, 0 ≤ c m := fun m => by
      rw [hc' m]; exact mul_nonneg (hgap0 m) (gnn _ (pow_nonneg hx0.le _))
    have ha_le : ∀ m, a m ≤ x^m := fun m => by
      rw [ha' m]
      have h1 := gle (x^(m+1)) (pow_nonneg hx0.le _)
      have h2 : x^(m+1) ≤ 1 := le_trans (hxs m) (hxm1 m)
      have := mul_le_mul_of_nonneg_left (show g (x^(m+1)) ≤ 1 by linarith) (hgap0 m)
      linarith [hxm0 m, hxs m, pow_nonneg hx0.le (m+1)]
    have hc_le : ∀ m, c m ≤ x^m := fun m => by
      rw [hc' m]
      have h1 := gle (x^m) (pow_nonneg hx0.le _)
      have := mul_le_mul_of_nonneg_left (show g (x^m) ≤ 1 by linarith [hxm1 m]) (hgap0 m)
      linarith [hxm0 m, hxs m, pow_nonneg hx0.le (m+1)]
    have hsa : Summable a :=
      Summable.of_nonneg_of_le ha_nn ha_le (summable_geometric_of_lt_one hx0.le hx1)
    have hsc : Summable c :=
      Summable.of_nonneg_of_le hc_nn hc_le (summable_geometric_of_lt_one hx0.le hx1)
    have tele : ∀ f : ℝ → ℝ, ∀ N, ∑ m ∈ Finset.range N, (f (x^m) - f (x^(m+1))) = f 1 - f (x^N) := by
      intro f N
      induction N with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    have hP : ∀ N, ∑ m ∈ Finset.range N, a m ≤ G 1 - G (x^N) := fun N =>
      (Finset.sum_le_sum fun m _ => (hterm m).1).trans_eq (tele G N)
    have hQ : ∀ N, G 1 - G (x^N) ≤ ∑ m ∈ Finset.range N, c m := fun N =>
      (tele G N).symm.le.trans (Finset.sum_le_sum fun m _ => (hterm m).2.1)
    have hQP : ∀ N, ∑ m ∈ Finset.range N, c m ≤ ∑ m ∈ Finset.range N, a m + (1 - x) * g 1 := by
      intro N
      have e1 := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range N) => (hterm m).2.2)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, tele g N] at e1
      have e2 : 0 ≤ g (x^N) := gnn _ (pow_nonneg hx0.le _)
      nlinarith [mul_nonneg (sub_nonneg.2 hx1.le) e2]
    have hlim : Filter.Tendsto (fun N : ℕ => G (x^N)) Filter.atTop (nhds 0) := by
      have h := ((hGd 0 (by norm_num)).continuousAt.tendsto).comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1)
      rw [G0] at h; exact h
    have hsA := hsa.hasSum.tendsto_sum_nat
    have hsC := hsc.hasSum.tendsto_sum_nat
    have hA_le : ∑' i, a i ≤ G 1 - 0 :=
      le_of_tendsto_of_tendsto' hsA (tendsto_const_nhds.sub hlim) (fun N => hP N)
    have hB_ge : G 1 - 0 ≤ ∑' i, c i :=
      le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub hlim) hsC (fun N => hQ N)
    have hBA : ∑' i, c i ≤ ∑' i, a i + (1 - x) * g 1 :=
      le_of_tendsto_of_tendsto' hsC (hsA.add tendsto_const_nhds) (fun N => hQP N)
    rw [sub_zero, G1] at hA_le hB_ge
    rw [g1] at hBA
    have hz : Filter.Tendsto (fun N : ℕ => x ^ N * g (x ^ (N+1))) Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun N => mul_nonneg (pow_nonneg hx0.le _) (gnn _ (pow_nonneg hx0.le _)))
        (fun N => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1)
      have h1 := gle (x^(N+1)) (pow_nonneg hx0.le _)
      have h2 : x^(N+1) ≤ 1 := le_trans (hxs N) (hxm1 N)
      exact mul_le_of_le_one_right (pow_nonneg hx0.le N) (by linarith)
    have SBP' : ∀ N : ℕ, ∑ n ∈ Finset.range (N+1), x ^ n * (g (x ^ (n + 1)) - g (x ^ n))
        = x ^ N * g (x ^ (N+1)) - g 1 + ∑ m ∈ Finset.range N, a m := by
      intro N; rw [SBP x N]; simp only [ha']
    have hS : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1), x ^ n * (g (x ^ (n + 1)) - g (x ^ n)))
        Filter.atTop (nhds (0 - g 1 + ∑' i, a i)) := by
      refine Filter.Tendsto.congr (fun N => (SBP' N).symm) ?_
      exact ((hz.sub_const (g 1)).add hsA)
    have e1 : Filter.Tendsto (fun N : ℕ => ∏ n ∈ Finset.range (N+1), ((1 + x ^ (n + 1)) / (1 + x ^ n)) ^ (x ^ n))
        Filter.atTop (nhds (xprod x)) :=
      (hxprod x ⟨hx0, hx1⟩).comp (Filter.tendsto_add_atTop_nat 1)
    have e1' := e1.congr (fun N => P1 x hx0 hx1 (N+1))
    have e2 : Filter.Tendsto (fun N : ℕ => Real.exp (∑ n ∈ Finset.range (N+1), x ^ n * (g (x ^ (n + 1)) - g (x ^ n))))
        Filter.atTop (nhds (Real.exp (0 - g 1 + ∑' i, a i))) :=
      (Real.continuous_exp.tendsto _).comp hS
    have hxeq : xprod x = Real.exp (0 - g 1 + ∑' i, a i) := tendsto_nhds_unique e1' e2
    rw [hxeq, g1]
    constructor
    · apply Real.exp_le_exp.2
      linarith [hBA, hB_ge, hA_le]
    · apply Real.exp_le_exp.2
      linarith [hA_le]
  have hlo : Filter.Tendsto (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x) * Real.log 2))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (Real.exp (Real.log 2 - 1))) := by
    have hc : Continuous (fun x : ℝ => Real.exp (Real.log 2 - 1 - (1 - x) * Real.log 2)) := by
      fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
    simpa using this
  have hhi : Filter.Tendsto (fun _ : ℝ => Real.exp (Real.log 2 - 1)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (Real.exp (Real.log 2 - 1))) := tendsto_const_nhds
  have hev : ∀ᶠ x in nhdsWithin (1:ℝ) (Set.Iio 1), x ∈ Set.Ioo (0:ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  have hfin := tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (hev.mono fun x hx => (main x hx).1) (hev.mono fun x hx => (main x hx).2)
  have hval : Real.exp (Real.log 2 - 1) = putnam_2004_b5_solution := by
    unfold putnam_2004_b5_solution
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [hval] at hfin
  exact hfin
