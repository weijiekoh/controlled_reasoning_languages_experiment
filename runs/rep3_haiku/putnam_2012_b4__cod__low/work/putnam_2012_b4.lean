import Mathlib

open Matrix Function Real Topology Filter

noncomputable abbrev putnam_2012_b4_solution : Prop := True
/--
Suppose that $a_0 = 1$ and that $a_{n+1} = a_n + e^{-a_n}$ for $n=0,1,2,\dots$. Does $a_n - \log n$
have a finite limit as $n \to \infty$? (Here $\log n = \log_e n = \ln n$.)
-/
theorem putnam_2012_b4
(a : ℕ → ℝ)
(ha0 : a 0 = 1)
(han : ∀ n : ℕ, a (n + 1) = a n + exp (-a n))
: ((∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ putnam_2012_b4_solution) := by
  have hx : ∀ k : ℕ, exp (a (k+1)) = exp (a k) * exp (1 / exp (a k)) := by
    intro k; rw [han k, Real.exp_add, one_div, Real.exp_neg]
  have hpos : ∀ k : ℕ, 0 < exp (a k) := fun k => Real.exp_pos _
  have hlow : ∀ k : ℕ, (k:ℝ) + 1 ≤ exp (a k) := by
    intro k
    induction k with
    | zero => rw [ha0, Nat.cast_zero]; linarith [Real.add_one_le_exp 1]
    | succ k ih =>
      rw [hx k]
      have h1 : 1 + 1 / exp (a k) ≤ exp (1 / exp (a k)) := by
        linarith [Real.add_one_le_exp (1 / exp (a k))]
      have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (hpos k))
      have e : exp (a k) * (1 + 1 / exp (a k)) = exp (a k) + 1 := by
        have : exp (a k) ≠ 0 := ne_of_gt (hpos k)
        field_simp
      push_cast
      linarith
  have hsq : ∀ k : ℕ, 1 / ((k:ℝ) + 1) + 3 * √((k:ℝ) + 1) ≤ 3 * √(((k:ℝ)+1) + 1) := by
    intro k
    have hk : (0:ℝ) ≤ k := by positivity
    set s := √((k:ℝ)+1) with hs
    set t := √(((k:ℝ)+1)+1) with ht
    have hs2 : s^2 = (k:ℝ)+1 := Real.sq_sqrt (by linarith)
    have ht2 : t^2 = (k:ℝ)+2 := by rw [ht, Real.sq_sqrt (by linarith)]; ring
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hs1 : 1 ≤ s := by nlinarith
    have hst : s ≤ t := Real.sqrt_le_sqrt (by linarith)
    have h2t : 2 * t ≤ 3 * ((k:ℝ)+1) := by nlinarith
    have key : (t - s) * (t + s) = 1 := by nlinarith
    have hts : 0 < t + s := by linarith
    have h3 : t + s ≤ 3 * ((k:ℝ)+1) := by linarith
    rw [div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hst) hk]
  have hup : ∀ k : ℕ, exp (a k) ≤ (k:ℝ) + 3 * √((k:ℝ) + 1) := by
    intro k
    induction k with
    | zero =>
      rw [ha0, Nat.cast_zero, zero_add, zero_add, Real.sqrt_one]
      linarith [Real.exp_one_lt_d9]
    | succ k ih =>
      have hxk := hlow k
      have hx1 : 1 ≤ exp (a k) := by
        have : (0:ℝ) ≤ k := by positivity
        linarith
      have hx0 : exp (a k) ≠ 0 := ne_of_gt (hpos k)
      have ht : 1 / exp (a k) ≤ 1 := by
        rw [div_le_one (hpos k)]; exact hx1
      have ht0 : 0 ≤ 1 / exp (a k) := by positivity
      have hexp : exp (1 / exp (a k)) ≤ 1 + 1 / exp (a k) + (1 / exp (a k))^2 := by
        have h := Real.abs_exp_sub_one_sub_id_le (x := 1 / exp (a k))
          (by rw [abs_of_nonneg ht0]; exact ht)
        have := (abs_le.mp h).2
        linarith
      have hinv : 1 / exp (a k) ≤ 1 / ((k:ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hxk
      have hstep : exp (a (k+1)) ≤ exp (a k) + 1 + 1 / exp (a k) := by
        rw [hx k]
        have h := mul_le_mul_of_nonneg_left hexp (le_of_lt (hpos k))
        have e : exp (a k) * (1 + 1 / exp (a k) + (1 / exp (a k))^2)
            = exp (a k) + 1 + 1 / exp (a k) := by
          field_simp
        linarith
      have := hsq k
      push_cast
      linarith
  have hfb : ∀ k : ℕ, 1 ≤ k →
      -(12 / (√((k:ℝ)+1))^3) ≤ (a (k+1) - Real.log ((k+1 : ℕ):ℝ)) - (a k - Real.log (k:ℝ)) ∧
      (a (k+1) - Real.log ((k+1 : ℕ):ℝ)) - (a k - Real.log (k:ℝ)) ≤ 12 / (√((k:ℝ)+1))^3 := by
    intro k hk1
    have hK : (1:ℝ) ≤ k := by exact_mod_cast hk1
    have hKp : (0:ℝ) < k := by linarith
    have hs2 : (√((k:ℝ)+1))^2 = (k:ℝ)+1 := Real.sq_sqrt (by linarith)
    set s := √((k:ℝ)+1) with hs
    have hs1 : 1 ≤ s := by nlinarith [Real.sqrt_nonneg ((k:ℝ)+1)]
    have hs3 : 0 < s^3 := by positivity
    set x := exp (a k) with hxdef
    have hxk := hlow k
    have hxu := hup k
    rw [← hxdef] at hxu
    have hxpos : 0 < x := hpos k
    have hdiff : a (k+1) - a k = 1 / x := by rw [han k, one_div, Real.exp_neg]; ring_nf; rfl
    have hcast : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hL1 : Real.log ((k:ℝ)+1) - Real.log k ≤ 1 / k := by
      have := Real.log_le_sub_one_of_pos (x := ((k:ℝ)+1)/k) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at this
      have e : ((k:ℝ)+1)/k - 1 = 1/k := by field_simp; ring
      linarith
    have hL2 : 1 / ((k:ℝ)+1) ≤ Real.log ((k:ℝ)+1) - Real.log k := by
      have := Real.log_le_sub_one_of_pos (x := (k:ℝ)/((k:ℝ)+1)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at this
      have e : (k:ℝ)/((k:ℝ)+1) - 1 = -(1/((k:ℝ)+1)) := by field_simp; ring
      linarith
    have hinvx : 1 / x ≤ 1 / ((k:ℝ)+1) := one_div_le_one_div_of_le (by positivity) hxk
    have hinvx2 : 1 / ((k:ℝ) + 3 * s) ≤ 1 / x := one_div_le_one_div_of_le hxpos hxu
    constructor
    · -- lower bound
      have h1 : 1 / k - 1 / x ≤ 12 / s^3 := by
        rw [div_sub_div _ _ (ne_of_gt hKp) (ne_of_gt hxpos), div_le_div_iff₀ (by positivity) hs3]
        have hxK : (k:ℝ) + 1 ≤ x := hxk
        nlinarith [mul_nonneg (sub_nonneg.mpr hxu) hs3.le, mul_nonneg hKp.le (sub_nonneg.mpr hxK),
          mul_nonneg (sub_nonneg.mpr hs1) hKp.le, sq_nonneg (s^2)]
      have h2 : 1 / x - Real.log ((k:ℝ)+1) + Real.log k ≥ 1 / x - 1 / k := by linarith
      have h3 : 1 / k ≥ 1 / x - 0 := by
        have : 1 / x ≤ 1 / k := one_div_le_one_div_of_le hKp (by linarith)
        linarith
      have : -(12 / s^3) ≤ 1 / x - 1 / k := by linarith
      have e : 1 / x - Real.log ((k:ℝ)+1) + Real.log k = 1 / x - (Real.log ((k:ℝ)+1) - Real.log k) := by ring
      have hpos12 : (0:ℝ) ≤ 12 / s^3 := by positivity
      linarith
    · have hpos12 : (0:ℝ) ≤ 12 / s^3 := by positivity
      linarith
  have hg : Summable (fun k : ℕ => 12 / (√((k:ℝ)+1))^3) := by
    have hs : ∀ y : ℝ, 0 ≤ y → (√y)^3 = y^(3/2:ℝ) := by
      intro y hy
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
      norm_num
    have := (Real.summable_one_div_nat_add_rpow 1 (3/2)).mpr (by norm_num)
    have := this.mul_left 12
    refine this.congr (fun k => ?_)
    rw [hs _ (by positivity)]
    have : |(k:ℝ) + 1| = (k:ℝ) + 1 := abs_of_nonneg (by positivity)
    rw [this]
    ring
  have hsum : Summable (fun k : ℕ => (a (k+1) - Real.log ((k+1 : ℕ):ℝ)) - (a k - Real.log (k:ℝ))) := by
    refine Summable.of_norm_bounded_eventually_nat hg ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    rw [Real.norm_eq_abs, abs_le]
    exact hfb k hk
  have hb : ∀ n : ℕ, a n - Real.log n = (a 0 - Real.log ((0:ℕ):ℝ)) +
      ∑ i ∈ Finset.range n, ((a (i+1) - Real.log ((i+1 : ℕ):ℝ)) - (a i - Real.log (i:ℝ))) := by
    intro n
    have := Finset.sum_range_sub (fun m : ℕ => a m - Real.log (m:ℝ)) n
    linarith
  have ht := hsum.hasSum.tendsto_sum_nat
  have ht' := (tendsto_const_nhds (x := a 0 - Real.log ((0:ℕ):ℝ))).add ht
  simp only [putnam_2012_b4_solution, iff_true]
  exact ⟨_, Tendsto.congr (fun n => (hb n).symm) ht'⟩
