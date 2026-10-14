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
  have hk0 : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (1:ℝ)/k := ⟨_, rfl⟩
  rw [← hq] at ha
  have hq0 : 0 < q := by rw [hq]; exact div_pos one_pos hk0
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 + q := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  have hpq : p - 1 = q := by rw [hp]; ring
  have key : ∀ x h : ℝ, 0 < x → -x ≤ h → ∀ r : ℝ, 1 ≤ r →
      x^r + r * (x^(r-1) * h) ≤ (x+h)^r := by
    intro x h hx hh r hr
    have hs : -1 ≤ h/x := by rw [le_div_iff₀ hx]; linarith
    have hb := one_add_mul_self_le_rpow_one_add hs hr
    have e : (1 + h/x) = (x+h)/x := by field_simp
    have hxp : 0 < x^r := Real.rpow_pos_of_pos hx r
    rw [e, Real.div_rpow (by linarith) hx.le, le_div_iff₀ hxp] at hb
    have e2 : x^(r-1) = x^r / x := Real.rpow_sub_one hx.ne' r
    rw [e2]
    have e3 : r * (x^r/x * h) = r*(h/x) * x^r := by ring
    linarith [hb, e3]
  have hpos : ∀ n, 0 < a n := by
    intro n
    induction n with
    | zero => exact ha0
    | succ m ih =>
      rw [ha m]
      have : 0 < 1/((a m)^q) := one_div_pos.mpr (Real.rpow_pos_of_pos ih q)
      linarith
  have hR : ∀ n, 0 < (a n)^q := fun n => Real.rpow_pos_of_pos (hpos n) q
  have hstep : ∀ n, a (n+1) = a n + 1/(a n)^q := fun n => ha n
  have lower : ∀ n, a n ^ p + p ≤ a (n+1) ^ p := by
    intro n
    have hx := hpos n
    have hh : 0 < 1/(a n)^q := one_div_pos.mpr (hR n)
    have h := key (a n) (1/(a n)^q) hx (by linarith) p hp1
    rw [hpq] at h
    have e : (a n)^q * (1/(a n)^q) = 1 := by field_simp [(hR n).ne']
    rw [e, mul_one, ← hstep n] at h
    linarith
  have hy_lin : ∀ n : ℕ, (n:ℝ) * p ≤ (a n)^p := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul]
      exact (Real.rpow_pos_of_pos (hpos 0) p).le
    | succ m ih =>
      push_cast
      rw [add_mul, one_mul]
      linarith [lower m]
  have hmono : Monotone a := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hstep n]
    have := one_div_pos.mpr (hR n)
    linarith
  have htop : Tendsto a atTop atTop := by
    apply tendsto_atTop_atTop_of_monotone hmono
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (max b 0 ^ p)
    refine ⟨N, ?_⟩
    by_contra hcon
    push Not at hcon
    have h1 : a N ^ p < (max b 0)^p :=
      Real.rpow_lt_rpow (hpos N).le (lt_of_lt_of_le hcon (le_max_left _ _)) (by linarith)
    have h2 := hy_lin N
    have h3 : (N:ℝ) ≤ N * p := by
      have : (0:ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    linarith
  have ht : Tendsto (fun n => (1/(a n)^q)/a n) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (1:ℝ)/a n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop htop
    refine squeeze_zero' ?_ ?_ hinv
    · exact Eventually.of_forall (fun n => (div_pos (one_div_pos.mpr (hR n)) (hpos n)).le)
    · have hev : ∀ᶠ n in atTop, 1 ≤ a n := htop.eventually_ge_atTop 1
      refine hev.mono (fun n hn => ?_)
      have h1 : 1 ≤ (a n)^q := Real.one_le_rpow hn hq0.le
      show (1/(a n)^q)/a n ≤ 1/a n
      rw [div_div]
      apply one_div_le_one_div_of_le (hpos n)
      nlinarith [hpos n]
  have hr : Tendsto (fun n => (1 + (1/(a n)^q)/a n)^q) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1:ℝ))).add ht).rpow_const (Or.inr hq0.le)
    simpa using this
  have dlow : ∀ n, p ≤ a (n+1)^p - a n^p := fun n => by linarith [lower n]
  have dup : ∀ n, a (n+1)^p - a n^p ≤ p * (1 + (1/(a n)^q)/a n)^q := by
    intro n
    have hx := hpos n
    have hx' := hpos (n+1)
    have hh : 0 < 1/(a n)^q := one_div_pos.mpr (hR n)
    have k1 := key (a (n+1)) (-(1/(a n)^q)) hx' (by rw [hstep n]; linarith) p hp1
    have ea : a (n+1) + -(1/(a n)^q) = a n := by rw [hstep n]; ring
    rw [ea, hpq] at k1
    have e0 : 1 + (1/(a n)^q)/a n = a (n+1) / a n := by
      rw [hstep n]; field_simp
    have e1 : a (n+1)^q * (1/(a n)^q) = (1 + (1/(a n)^q)/a n)^q := by
      rw [e0, Real.div_rpow hx'.le hx.le]; ring
    rw [mul_neg, e1] at k1
    linarith
  have hd : Tendsto (fun n => a (n+1)^p - a n^p) atTop (𝓝 p) := by
    have hup : Tendsto (fun n => p * (1 + (1/(a n)^q)/a n)^q) atTop (𝓝 (p*1)) :=
      hr.const_mul p
    rw [mul_one] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup dlow dup
  have hces := hd.cesaro
  have htel : ∀ n, ∑ i ∈ Finset.range n, (a (i+1)^p - a i^p) = a n^p - a 0^p :=
    fun n => Finset.sum_range_sub (fun i => a i ^ p) n
  have hz : Tendsto (fun n : ℕ => a 0 ^ p * (n:ℝ)⁻¹) atTop (𝓝 (a 0 ^ p * 0)) :=
    ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0))).const_mul _
  rw [mul_zero] at hz
  have h3 := hces.add hz
  rw [add_zero] at h3
  have hZ : Tendsto (fun n : ℕ => a n ^ p * (n:ℝ)⁻¹) atTop (𝓝 p) := by
    refine h3.congr (fun n => ?_)
    rw [htel n]
    ring
  have hpk : p^k = putnam_2006_b6_solution k := by
    simp only [putnam_2006_b6_solution]
    rw [hp, hq]
    congr 1
    field_simp
  have hyk : ∀ n : ℕ, (a n ^ p)^k = a n ^ (k+1) := by
    intro n
    calc (a n ^ p)^k = (a n ^ p)^((k:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
      _ = a n ^ (p * k) := (Real.rpow_mul (hpos n).le _ _).symm
      _ = a n ^ (((k+1 : ℕ)) : ℝ) := by
          congr 1
          rw [hp, hq]
          push_cast
          field_simp
      _ = a n ^ (k+1) := Real.rpow_natCast _ _
  have hfin := hZ.pow k
  rw [← hpk]
  refine hfin.congr (fun n => ?_)
  rw [mul_pow, hyk n, inv_pow, div_eq_mul_inv]
