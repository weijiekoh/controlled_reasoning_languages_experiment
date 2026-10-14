import Mathlib

open Set Topology Filter

noncomputable abbrev putnam_2006_b6_solution : ℕ → ℝ := fun k => ((k+1)/k)^k
/--
Let $k$ be an integer greater than 1. Suppose $a_0 > 0$, and define \[ a_{n+1} = a_n + \frac{1}{\sqrt[k]{a_n}} \] for $n > 0$. Evaluate \[\lim_{n \to \infty} \frac{a_n^{k+1}}{n^k}.\]
-/
theorem putnam_2006_b6
(k : ℕ)
(hk : k > 1)
(a : ℕ → ℝ)
(ha0 : a 0 > 0)
(ha : ∀ n : ℕ, a (n + 1) = a n + 1/((a n)^((1 : ℝ)/k)))
: Tendsto (fun n => (a n)^(k+1)/(n ^ k)) atTop (𝓝 (putnam_2006_b6_solution k)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk0' : (k:ℝ) ≠ 0 := hk0.ne'
  set q : ℝ := (1:ℝ)/k with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  set p : ℝ := 1 + q with hp
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  have key : ∀ x : ℝ, 0 < x →
      p ≤ (x + 1/x^q)^p - x^p ∧ (x + 1/x^q)^p - x^p ≤ p * ((x + 1/x^q)/x)^q := by
    intro x hx
    have hxq : 0 < x^q := Real.rpow_pos_of_pos hx q
    have hX : x^p = x * x^q := by rw [hp, Real.rpow_add hx, Real.rpow_one]
    have hh : 0 < 1/x^q := by positivity
    obtain ⟨y, hy⟩ : ∃ y, y = x + 1/x^q := ⟨_, rfl⟩
    rw [← hy]
    have hy0 : 0 < y := by linarith
    have hd : y - x = 1/x^q := by linarith
    have hYp : y^p = y * y^q := by rw [hp, Real.rpow_add hy0, Real.rpow_one]
    have hXpos : 0 < x^p := Real.rpow_pos_of_pos hx p
    have hYpos : 0 < y^p := Real.rpow_pos_of_pos hy0 p
    have hdiv1 : (y/x)^p = y^p / x^p := Real.div_rpow hy0.le hx.le p
    have hdiv2 : (x/y)^p = x^p / y^p := Real.div_rpow hx.le hy0.le p
    have hdiv3 : (y/x)^q = y^q / x^q := Real.div_rpow hy0.le hx.le q
    have hB1 := one_add_mul_self_le_rpow_one_add (s := y/x - 1)
      (by have : 0 < y/x := by positivity
          linarith) hp1
    have hB2 := one_add_mul_self_le_rpow_one_add (s := x/y - 1)
      (by have : 0 < x/y := by positivity
          linarith) hp1
    have e1 : 1 + (y/x - 1) = y/x := by ring
    have e2 : 1 + (x/y - 1) = x/y := by ring
    rw [e1, hdiv1, le_div_iff₀ hXpos] at hB1
    rw [e2, hdiv2, le_div_iff₀ hYpos] at hB2
    have f1 : (1 + p*(y/x - 1)) * x^p = x^p + p := by
      have : y/x - 1 = (1/x^q)/x := by rw [← hd]; field_simp
      rw [this, hX]; field_simp
    have f2 : (1 + p*(x/y - 1)) * y^p = y^p - p * (y^q/x^q) := by
      have : (1 + p*(x/y - 1)) * y = y - p * (y - x) := by field_simp; ring
      rw [hYp]
      have h3 : (1 + p*(x/y - 1)) * (y * y^q) = ((1 + p*(x/y - 1)) * y) * y^q := by ring
      rw [h3, this, hd]
      field_simp
    constructor
    · nlinarith
    · rw [hdiv3]
      nlinarith
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ m ih =>
      rw [ha m]
      have : 0 < (a m)^q := Real.rpow_pos_of_pos ih q
      have : 0 < 1/(a m)^q := by positivity
      linarith
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [ha n]
    have : 0 < 1/(a n)^q := by have := Real.rpow_pos_of_pos (hpos n) q; positivity
    linarith
  have hunb : Tendsto a atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro M
    by_contra hcon
    push_neg at hcon
    have hbd : ∀ n, a n < M := fun n => by
      obtain ⟨m, hm, hlt⟩ := hcon n
      exact lt_of_le_of_lt (hmono hm) hlt
    have hMpos : 0 < M := lt_trans (hpos 0) (hbd 0)
    have hc : 0 < 1/M^q := by positivity
    have hlow : ∀ n : ℕ, a 0 + n * (1/M^q) ≤ a n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [ha m]
        push_cast
        have h1 : 1/M^q ≤ 1/(a m)^q :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hpos m) q)
            (Real.rpow_le_rpow (hpos m).le (hbd m).le hq0.le)
        have h2 : ((m:ℝ)+1)*(1/M^q) = m*(1/M^q) + 1/M^q := by ring
        linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (M / (1/M^q))
    rw [div_lt_iff₀ hc] at hN
    have := hlow N
    linarith [hbd N, hpos 0]
  have hinv : Tendsto (fun n => 1 + (a n)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).add (tendsto_inv_atTop_zero.comp hunb)
  have hratio : Tendsto (fun n => a (n+1) / a n) atTop (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · refine Eventually.of_forall (fun n => ?_)
      rw [le_div_iff₀ (hpos n), ha n]
      have : 0 < 1/(a n)^q := by have := Real.rpow_pos_of_pos (hpos n) q; positivity
      nlinarith [hpos n]
    · have hev : ∀ᶠ n in atTop, 1 ≤ a n := (tendsto_atTop.1 hunb) 1
      filter_upwards [hev] with n hn
      rw [div_le_iff₀ (hpos n), ha n]
      have hq1 : 1 ≤ (a n)^q := Real.one_le_rpow hn hq0.le
      have h3 : 1/(a n)^q ≤ 1 := by rw [div_le_one (by linarith)]; exact hq1
      have h4 : (1 + (a n)⁻¹) * a n = a n + 1 := by field_simp
      have h5 : 1/(a n)^q ≤ 1/(a n)^q := le_refl _
      have h6 : 1/(a n)^q * (a n)^q = 1 := by field_simp
      nlinarith [hpos n, mul_le_mul_of_nonneg_left hq1 (le_of_lt (hpos n))]
  have hup : Tendsto (fun n => p * ((a (n+1))/(a n))^q) atTop (𝓝 p) := by
    have := (hratio.rpow_const (Or.inr hq0.le)).const_mul p
    simpa using this
  have hd : Tendsto (fun n => (a (n+1))^p - (a n)^p) atTop (𝓝 p) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
    · have := key (a n) (hpos n)
      rw [← ha n] at this
      exact this.1
    · have := key (a n) (hpos n)
      rw [← ha n] at this
      exact this.2
  have hC := hd.cesaro
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((a (i+1))^p - (a i)^p) = (a n)^p - (a 0)^p :=
    fun n => Finset.sum_range_sub (fun i => (a i)^p) n
  simp only [hsum] at hC
  have hB : Tendsto (fun n:ℕ => (a n)^p / (n:ℝ)) atTop (𝓝 p) := by
    have h0 : Tendsto (fun n:ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := hC.add (h0.const_mul ((a 0)^p))
    simp only [mul_zero, add_zero] at this
    refine Tendsto.congr (fun n => ?_) this
    ring
  have hpk : ∀ n : ℕ, ((a n)^p)^k = (a n)^(k+1) := by
    intro n
    have hn := hpos n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_natCast]
    congr 1
    rw [hp, hq]
    push_cast
    field_simp
  have hfin := hB.pow k
  have hlim : p^k = putnam_2006_b6_solution k := by
    unfold putnam_2006_b6_solution
    congr 1
    rw [hp, hq]
    field_simp
  rw [hlim] at hfin
  refine Tendsto.congr (fun n => ?_) hfin
  rw [div_pow, hpk]
