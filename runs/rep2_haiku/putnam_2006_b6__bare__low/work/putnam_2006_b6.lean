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
  have hkpos : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1/(k:ℝ) := ⟨_, rfl⟩
  rw [← hq] at ha
  have hq0 : 0 < q := by rw [hq]; positivity
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hkpos]; exact_mod_cast (by omega : 1 ≤ k)
  -- key two-sided estimate
  have key : ∀ x : ℝ, 0 < x →
      x^(1+q) + (1+q) ≤ (x + 1/x^q)^(1+q) ∧
      (x + 1/x^q)^(1+q) ≤ x^(1+q) + (1+q) + q / x^(1+q) := by
    intro x hx
    have ht : 0 < x^q := Real.rpow_pos_of_pos hx q
    have hxp : x^(1+q) = x * x^q := by rw [Real.rpow_add hx, Real.rpow_one]
    obtain ⟨t, htdef⟩ : ∃ t, t = x^q := ⟨_, rfl⟩
    rw [← htdef] at ht ⊢
    rw [← htdef] at hxp
    have hy : x + 1/t = x * (1 + 1/(x*t)) := by field_simp
    have hs' : (-1:ℝ) ≤ 1/(x*t) := by
      have : 0 < 1/(x*t) := by positivity
      linarith
    constructor
    · have hb := one_add_mul_self_le_rpow_one_add hs' (p := 1+q) (by linarith)
      rw [hy, Real.mul_rpow hx.le (by positivity), hxp]
      have h1 : 0 ≤ x * t := by positivity
      have : x * t * (1 + (1+q) * (1/(x*t))) = x*t + (1+q) := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hb h1]
    · have hb := rpow_one_add_le_one_add_mul_self hs' (p := q) hq0.le hq1
      have hyq : (x + 1/t)^(1+q) = (x + 1/t) * (x + 1/t)^q := by
        rw [Real.rpow_add (by positivity), Real.rpow_one]
      have hyq2 : (x + 1/t)^q = t * (1 + 1/(x*t))^q := by
        rw [hy, Real.mul_rpow hx.le (by positivity), ← htdef]
      rw [hyq, hyq2, hxp]
      have hpos : 0 ≤ x + 1/t := by positivity
      have h3 : (x + 1/t) * (t * (1 + 1/(x*t))^q) ≤ (x + 1/t) * (t * (1 + q * (1/(x*t)))) := by
        apply mul_le_mul_of_nonneg_left _ hpos
        exact mul_le_mul_of_nonneg_left hb ht.le
      have h4 : (x + 1/t) * (t * (1 + q * (1/(x*t)))) = x*t + (1+q) + q/(x*t) := by
        field_simp
        ring
      rw [h4] at h3
      exact h3
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      rw [ha n]
      have : 0 < 1/(a n)^q := div_pos one_pos (Real.rpow_pos_of_pos ih q)
      linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℝ, ∀ n, b n = (a n)^(1+q) := ⟨fun n => (a n)^(1+q), fun n => rfl⟩
  have hbrec : ∀ n, b (n+1) = (a n + 1/(a n)^q)^(1+q) := fun n => by rw [hbdef, ha n]
  have hb_lo : ∀ n, b n + (1+q) ≤ b (n+1) := fun n => by
    rw [hbrec n, hbdef n]; exact (key (a n) (hpos n)).1
  have hb_up : ∀ n, b (n+1) ≤ b n + (1+q) + q / b n := fun n => by
    rw [hbrec n, hbdef n]; exact (key (a n) (hpos n)).2
  have hbgrow : ∀ n : ℕ, b 0 + n*(1+q) ≤ b n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; linarith [hb_lo n]
  have hbtop : Tendsto b atTop atTop := by
    apply tendsto_atTop_mono hbgrow
    exact tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith : (0:ℝ) < 1+q))
  have hlim : Tendsto (fun n => q / b n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hbtop
  have hup' : Tendsto (fun n => (1+q) + q / b n) atTop (𝓝 ((1+q) + 0)) :=
    tendsto_const_nhds.add hlim
  rw [add_zero] at hup'
  have hd : Tendsto (fun n => b (n+1) - b n) atTop (𝓝 (1+q)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup'
    · exact Eventually.of_forall (fun n => by linarith [hb_lo n])
    · exact Eventually.of_forall (fun n => by linarith [hb_up n])
  have hC := hd.cesaro
  simp_rw [Finset.sum_range_sub] at hC
  have hinv : Tendsto (fun n:ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hB : Tendsto (fun n:ℕ => b n / n) atTop (𝓝 (1+q)) := by
    have h2 := hC.add (tendsto_const_nhds (x := b 0) |>.mul hinv)
    rw [mul_zero, add_zero] at h2
    refine Tendsto.congr (fun n => ?_) h2
    ring
  have hpowk : ∀ x:ℝ, 0 < x → (x^(1+q))^k = x^(k+1) := by
    intro x hx
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_natCast]
    congr 1
    rw [hq]; push_cast; field_simp
  have hfun : (fun n:ℕ => (a n)^(k+1)/(n:ℝ)^k) = fun n => (b n / n)^k := by
    funext n
    rw [div_pow, hbdef n, hpowk (a n) (hpos n)]
  have hp : (1+q) = ((k:ℝ)+1)/k := by rw [hq]; field_simp
  have := hB.pow k
  rw [hp] at this
  rw [hfun]
  exact this
