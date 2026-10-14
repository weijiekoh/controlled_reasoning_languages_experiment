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
: Tendsto (fun n => (a n)^(k+1)/(n ^ k)) atTop (𝓝 (putnam_2006_b6_solution k)) :=
by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((k:ℝ)+1)/k := ⟨_, rfl⟩
  have hkR : (1:ℝ) < k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hk0 : (k:ℝ) ≠ 0 := ne_of_gt hkpos
  have hq1 : q = 1 + 1/(k:ℝ) := by rw [hq]; field_simp
  have hinvk : 0 < 1/(k:ℝ) := by positivity
  have hqge : 1 ≤ q := by rw [hq1]; linarith
  have hqpos : 0 < q := by linarith
  have key : ∀ x : ℝ, 0 < x → x^q + q ≤ (x + 1/x^((1:ℝ)/k))^q ∧
      (x + 1/x^((1:ℝ)/k))^q ≤ x^q + q + (k * x^q)⁻¹ := by
    intro x hx
    have hr : 0 < x^((1:ℝ)/k) := Real.rpow_pos_of_pos hx _
    have hxq : x^q = x * x^((1:ℝ)/k) := by
      rw [hq1, Real.rpow_add hx, Real.rpow_one]
    set r := x^((1:ℝ)/k) with hr_def
    have hh : r * (1/r) = 1 := by field_simp
    set s := (1/r)/x with hs
    have hspos : 0 < s := div_pos (div_pos one_pos hr) hx
    have hxs : x + 1/r = x * (1 + s) := by rw [hs]; field_simp
    have hxs1 : x^q * s = 1 := by rw [hxq, hs]; field_simp
    have hsinv : s = (x^q)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hxs1)
    have hxqpos : 0 < x^q := Real.rpow_pos_of_pos hx q
    have hpow : (x + 1/r)^q = x^q * (1+s)^q := by
      rw [hxs, Real.mul_rpow hx.le (by linarith)]
    rw [hpow]
    have hL := one_add_mul_self_le_rpow_one_add (show (-1:ℝ) ≤ s by linarith) hqge
    have hU : (1+s)^q ≤ (1+s) * (1 + (1/(k:ℝ))*s) := by
      rw [hq1, Real.rpow_add (by linarith), Real.rpow_one]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply rpow_one_add_le_one_add_mul_self (by linarith) hinvk.le
      rw [div_le_iff₀ hkpos]; linarith
    constructor
    · have h1 := mul_le_mul_of_nonneg_left hL hxqpos.le
      have e : x^q*(1+q*s) = x^q + q := by linear_combination q * hxs1
      linarith
    · have h2 := mul_le_mul_of_nonneg_left hU hxqpos.le
      have e : x^q * ((1+s)*(1+(1/(k:ℝ))*s)) = x^q + q + (1/(k:ℝ))*s := by
        linear_combination ((1 + 1/(k:ℝ)) + s/k) * hxs1 - hq1
      have e2 : (1/(k:ℝ))*s = (k * x^q)⁻¹ := by
        rw [hsinv, mul_inv, one_div]
      linarith
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      rw [ha n]
      have : 0 < 1/(a n)^((1:ℝ)/k) := by
        have := Real.rpow_pos_of_pos ih ((1:ℝ)/k)
        positivity
      linarith
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, ∀ n, b n = (a n)^q := ⟨_, fun n => rfl⟩
  have hbrec : ∀ n, b n + q ≤ b (n+1) ∧ b (n+1) ≤ b n + q + (k * b n)⁻¹ := by
    intro n
    simp only [hb, ha n]
    exact key (a n) (hpos n)
  have hb0 : 0 ≤ b 0 := by rw [hb]; exact (Real.rpow_pos_of_pos (hpos 0) _).le
  have hbq : ∀ n : ℕ, q * n ≤ b n := by
    intro n
    induction n with
    | zero => simpa using hb0
    | succ n ih =>
      push_cast
      linarith [(hbrec n).1]
  have hbtop : Tendsto b atTop atTop :=
    tendsto_atTop_mono hbq (tendsto_natCast_atTop_atTop.const_mul_atTop hqpos)
  have hd : Tendsto (fun n => b (n+1) - b n) atTop (nhds q) := by
    have h0 : Tendsto (fun n => (k * b n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (hbtop.const_mul_atTop hkpos)
    have h1 : Tendsto (fun n => q + (k * b n)⁻¹) atTop (nhds q) := by
      simpa using (tendsto_const_nhds (x := q)).add h0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    · intro n; linarith [(hbrec n).1]
    · intro n; linarith [(hbrec n).2]
  have hces := hd.cesaro
  have hsum : ∀ n, ∑ i ∈ Finset.range n, (b (i+1) - b i) = b n - b 0 :=
    fun n => Finset.sum_range_sub b n
  simp_rw [hsum] at hces
  have hB : Tendsto (fun n : ℕ => b n / n) atTop (nhds q) := by
    have hz : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * b 0) atTop (nhds 0) := by
      have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (b 0)
      simpa using this
    have hsum2 := hces.add hz
    rw [add_zero] at hsum2
    refine Tendsto.congr (fun n => ?_) hsum2
    ring
  have hfin := hB.pow k
  have hid : ∀ n : ℕ, (b n / n)^k = (a n)^(k+1)/(n:ℝ)^k := by
    intro n
    rw [div_pow, hb, ← Real.rpow_natCast (a n ^ q) k, ← Real.rpow_mul (hpos n).le]
    have e : q * (k:ℝ) = ((k+1 : ℕ) : ℝ) := by
      rw [hq]; push_cast; field_simp
    rw [e, Real.rpow_natCast]
  show Tendsto (fun n : ℕ => (a n)^(k+1)/(n:ℝ)^k) atTop (nhds ((((k:ℝ)+1)/k)^k))
  rw [← hq]
  exact Tendsto.congr (fun n => hid n) hfin
