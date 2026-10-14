import Mathlib

open Set Topology Filter

noncomputable abbrev putnam_2006_b6_solution : ℕ → ℝ := fun k => ((k+1)/k)^k
lemma key_bound (q x : ℝ) (hq : 0 < q) (hx : 0 < x) :
    (1 + q) ≤ (x + 1 / x ^ q) ^ (1 + q) - x ^ (1 + q) ∧
    (x + 1 / x ^ q) ^ (1 + q) - x ^ (1 + q) ≤ (1 + q) * (1 + 1 / x ^ (1 + q)) ^ q := by
  have hxq : 0 < x ^ q := Real.rpow_pos_of_pos hx q
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = 1 / x ^ q := ⟨_, rfl⟩
  rw [← hh]
  have hh0 : 0 < h := by rw [hh]; positivity
  have hxh : x ^ q * h = 1 := by rw [hh]; field_simp
  have hcont : ContinuousOn (fun t : ℝ => t ^ (1 + q)) (Set.Icc x (x + h)) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    right; linarith
  have hderiv : ∀ t ∈ Set.Ioo x (x + h),
      HasDerivAt (fun t : ℝ => t ^ (1 + q)) ((1 + q) * t ^ ((1 + q) - 1)) t := by
    intro t ht
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (by linarith [ht.1])))
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 + q))
    (fun t : ℝ => (1 + q) * t ^ ((1 + q) - 1)) (by linarith : x < x + h) hcont hderiv

  have hsub : x + h - x = h := by ring
  rw [hsub, eq_div_iff hh0.ne'] at hceq
  have hr : (1 + q) - 1 = q := by ring
  rw [hr] at hceq
  have hD : (x + h) ^ (1 + q) - x ^ (1 + q) = (1 + q) * c ^ q * h := by linarith
  have hlow : x ^ q ≤ c ^ q := Real.rpow_le_rpow hx.le hc.1.le hq.le
  have hup : c ^ q ≤ (x + h) ^ q := Real.rpow_le_rpow (by linarith [hc.1]) hc.2.le hq.le
  have h1q : (0:ℝ) ≤ (1 + q) * h := by nlinarith
  have hfact : (1 + q) * (x ^ q * h) = 1 + q := by rw [hxh, mul_one]
  have hE : (1 + 1 / x ^ (1 + q)) ^ q = (x + h) ^ q * h := by
    have e1 : 1 + 1 / x ^ (1 + q) = (x + h) / x := by
      rw [Real.rpow_add hx, Real.rpow_one, hh]
      field_simp
    rw [e1, Real.div_rpow (by linarith) hx.le, hh, div_eq_mul_one_div]
  rw [hE, hD]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlow h1q]
  · nlinarith [mul_le_mul_of_nonneg_left hup (by linarith : (0:ℝ) ≤ 1 + q), mul_le_mul_of_nonneg_right hup hh0.le]
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
  have hkne : (k:ℝ) ≠ 0 := by
    have : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    exact this.ne'
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = (1:ℝ) / k := ⟨_, rfl⟩
  have hq : 0 < q := by
    rw [hq_def]
    have : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  have ha' : ∀ n, a (n + 1) = a n + 1 / (a n) ^ q := fun n => by rw [ha n, hq_def]
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      rw [ha' n]
      have h1 := Real.rpow_pos_of_pos ih q
      have := one_div_pos.2 h1
      linarith
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, ∀ n, w n = (a n) ^ (1 + q) := ⟨_, fun n => rfl⟩
  have hstep : ∀ n, 1 + q ≤ w (n + 1) - w n ∧
      w (n + 1) - w n ≤ (1 + q) * (1 + 1 / w n) ^ q := by
    intro n
    have h := key_bound q (a n) hq (hpos n)
    rw [hw (n + 1), hw n, ha' n]
    exact h
  have hlow_all : ∀ n : ℕ, (n : ℝ) * (1 + q) ≤ w n := by
    intro n
    induction n with
    | zero =>
      have h0 := Real.rpow_pos_of_pos (hpos 0) (1 + q)
      rw [hw, Nat.cast_zero, zero_mul]
      exact h0.le
    | succ n ih =>
      push_cast
      have := (hstep n).1
      nlinarith
  have hwinf : Tendsto w atTop atTop :=
    tendsto_atTop_mono hlow_all
      (Filter.Tendsto.atTop_mul_const (by linarith) tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun n => 1 / w n) atTop (𝓝 0) := by
    simp only [one_div]
    exact hwinf.inv_tendsto_atTop
  have hU : Tendsto (fun n => (1 + q) * (1 + 1 / w n) ^ q) atTop (𝓝 (1 + q)) := by
    have h1 : Tendsto (fun n => 1 + 1 / w n) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    have := (h1.rpow_const (Or.inr hq.le)).const_mul (1 + q)
    simpa using this
  have hd : Tendsto (fun n => w (n + 1) - w n) atTop (𝓝 (1 + q)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
      (fun n => (hstep n).1) (fun n => (hstep n).2)
  have hces := hd.cesaro
  have hsum : ∀ n, ∑ i ∈ Finset.range n, (w (i + 1) - w i) = w n - w 0 :=
    fun n => Finset.sum_range_sub w n
  simp only [hsum] at hces
  have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h2 := hces.add (hz.const_mul (w 0))
  have h3 : (fun n : ℕ => (n : ℝ)⁻¹ * w n) =
      fun n : ℕ => (n : ℝ)⁻¹ * (w n - w 0) + w 0 * (n : ℝ)⁻¹ := by
    funext n; ring
  have hratio : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * w n) atTop (𝓝 (1 + q)) := by
    rw [h3]
    have h4 := h2
    rwa [mul_zero, add_zero] at h4
  have hfin := hratio.pow k
  have hwk : ∀ n : ℕ, (w n) ^ k = (a n) ^ (k + 1) := by
    intro n
    rw [hw n, ← Real.rpow_natCast, ← Real.rpow_mul (hpos n).le, ← Real.rpow_natCast]
    congr 1
    push_cast
    rw [hq_def]
    field_simp
  have heq : ∀ n : ℕ, ((n : ℝ)⁻¹ * w n) ^ k = (a n) ^ (k + 1) / ((n : ℝ) ^ k) := by
    intro n
    rw [mul_pow, inv_pow, hwk n, div_eq_inv_mul]
  have hfun : (fun n : ℕ => (a n) ^ (k + 1) / ((n : ℝ) ^ k)) =
      fun n : ℕ => ((n : ℝ)⁻¹ * w n) ^ k := funext (fun n => (heq n).symm)
  have hsol : putnam_2006_b6_solution k = (1 + q) ^ k := by
    unfold putnam_2006_b6_solution
    rw [hq_def, add_div, div_self hkne]
  rw [hfun, hsol]
  exact hfin
