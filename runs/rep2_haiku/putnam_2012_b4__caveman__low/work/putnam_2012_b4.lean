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
  simp only [putnam_2012_b4_solution, iff_true]
  have hYw : ∀ n, exp (a n) * exp (-a n) = 1 := fun n => by rw [← exp_add]; simp
  have hstep : ∀ n, exp (a (n+1)) = exp (a n) * exp (exp (-a n)) := fun n => by
    rw [han, exp_add]
  have hF1 : ∀ n : ℕ, (n:ℝ) + 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero => rw [ha0, Nat.cast_zero]; linarith [Real.add_one_le_exp (1:ℝ)]
    | succ n ih =>
      have hw0 := exp_pos (-a n)
      have h1 := Real.add_one_le_exp (exp (-a n))
      have h2 := hYw n
      have h3 := mul_le_mul_of_nonneg_left h1 (exp_pos (a n)).le
      rw [hstep n]; push_cast
      nlinarith
  have hsqrt : ∀ n : ℕ, 1 ≤ 2 * (√((n:ℝ)+1) - √(n:ℝ)) * ((n:ℝ)+1) := by
    intro n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have ht2 : (√((n:ℝ)+1))^2 = (n:ℝ)+1 := Real.sq_sqrt (by linarith)
    have hs2 : (√(n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt hn
    have hs0 : 0 ≤ √(n:ℝ) := Real.sqrt_nonneg _
    have ht0 : 0 ≤ √((n:ℝ)+1) := Real.sqrt_nonneg _
    have hst : √(n:ℝ) ≤ √((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
    generalize √((n:ℝ)+1) = t at *
    generalize √(n:ℝ) = s at *
    have ht1 : 1 ≤ t := by nlinarith
    have hprod : (t - s) * (t + s) = 1 := by nlinarith
    rw [← ht2]
    nlinarith [mul_nonneg (sub_nonneg.2 hst) (show 0 ≤ 2*t^2 - t - s by nlinarith)]
  have hZ : ∀ n : ℕ, exp (a n) - (n:ℝ) ≤ 3 + 2 * √(n:ℝ) := by
    intro n
    induction n with
    | zero =>
      have := Real.exp_one_lt_d9
      rw [ha0]
      norm_num at this ⊢
      linarith
    | succ n ih =>
      have hw0 : 0 < exp (-a n) := exp_pos _
      have hYn := hF1 n
      have hYw' := hYw n
      have hw1 : exp (-a n) ≤ 1 := by
        nlinarith [mul_nonneg hw0.le (show (0:ℝ) ≤ exp (a n) - 1 by
          linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])]
      have habs : |exp (-a n)| ≤ 1 := by rw [abs_of_pos hw0]; exact hw1
      have hE := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le habs)).2
      have hE' : exp (exp (-a n)) ≤ 1 + exp (-a n) + (exp (-a n))^2 := by linarith
      have h1 := mul_le_mul_of_nonneg_left hYn hw0.le
      have hwle : exp (-a n) ≤ 2 * (√((n:ℝ)+1) - √(n:ℝ)) := by
        have hm : exp (-a n) * ((n:ℝ)+1) ≤ (2 * (√((n:ℝ)+1) - √(n:ℝ))) * ((n:ℝ)+1) := by
          linarith [hsqrt n, h1, hYw']
        exact le_of_mul_le_mul_right hm (by positivity)
      have h3 : exp (a n) * (exp (-a n))^2 = exp (-a n) := by
        rw [sq, ← mul_assoc, hYw', one_mul]
      have h4 := mul_le_mul_of_nonneg_left hE' (exp_pos (a n)).le
      rw [hstep n]
      push_cast
      nlinarith
  have hpow : ∀ y : ℝ, 0 < y → y^((3:ℝ)/2) = y * √y := by
    intro y hy
    rw [Real.sqrt_eq_rpow, show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  have core : ∀ x s Y w L : ℝ, 1 ≤ s → x = s^2 → x + 1 ≤ Y → Y - x ≤ 3 + 2*s →
      w * Y = 1 → 0 < w → 1/(x+1) ≤ L → L ≤ 1/x → |w - L| ≤ 5 / s^3 := by
    intro x s Y w L hs1 hx hYx hr hwY hw hLlo hLhi
    have hx0 : 0 < x := by rw [hx]; nlinarith
    have hxu : x * (1/x) = 1 := mul_one_div_cancel hx0.ne'
    have hxv : (x+1) * (1/(x+1)) = 1 := mul_one_div_cancel (by linarith : (0:ℝ) < x+1).ne'
    have hu0 : 0 ≤ 1/x := by positivity
    have hv_le : 1/(x+1) ≤ 1/x := one_div_le_one_div_of_le hx0 (by linarith)
    have hw_x : w * x ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hYx hw.le]
    have hs3 : 5 / s^3 - (1/s^2)^2 * (3 + 2*s) = (3*s - 3) / s^4 := by
      have hs0 : s ≠ 0 := by linarith
      field_simp
      ring
    have hs3' : 0 ≤ (3*s - 3) / s^4 := div_nonneg (by linarith) (by positivity)
    generalize hu : 1/x = u at *
    generalize hv : 1/(x+1) = v at *
    have hwu : w ≤ u := by nlinarith
    have hr0 : 0 ≤ Y - x := by linarith
    have hdiff : u - w = u * w * (Y - x) := by linear_combination (-u) * hwY + w * hxu
    have hlow : -(u^2 * (3 + 2*s)) ≤ w - L := by
      nlinarith [mul_le_mul_of_nonneg_right hwu (mul_nonneg hu0 hr0),
        mul_le_mul_of_nonneg_left hr (sq_nonneg u)]
    have hid : u - v = u * v := by linear_combination v * hxu - u * hxv
    have hup : w - L ≤ u^2 := by
      nlinarith [mul_le_mul_of_nonneg_left hv_le hu0]
    have hsq0 : 0 ≤ u^2 * (2 + 2*s) := mul_nonneg (sq_nonneg u) (by linarith)
    have hfin : u^2 * (3 + 2*s) ≤ 5 / s^3 := by
      have hus : u = 1/s^2 := by rw [← hu, hx]
      rw [hus]
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → ℝ, ∀ k, g k = a (k+1) - Real.log ((k+1:ℕ):ℝ) :=
    ⟨_, fun k => rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, ∀ j, D j = g (j+1) - g j := ⟨_, fun j => rfl⟩
  have hsum : ∀ k, ∑ i ∈ Finset.range k, D i = g k - g 0 := by
    intro k
    simp only [hDdef]
    exact Finset.sum_range_sub g k
  have hD : ∀ j : ℕ, ‖D j‖ ≤ 5 * (1 / ((j+1:ℕ):ℝ)^((3:ℝ)/2)) := by
    intro j
    rw [hDdef j, hg_def, hg_def, Real.norm_eq_abs]
    have hx0 : (0:ℝ) < (j:ℝ)+1 := by positivity
    have hcx : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by push_cast; ring
    have hcx2 : ((j+1+1:ℕ):ℝ) = (j:ℝ)+1+1 := by push_cast; ring
    rw [hcx, hcx2, han (j+1), hpow _ hx0]
    have hF := hF1 (j+1)
    have hZj := hZ (j+1)
    push_cast at hF hZj
    have hs1 : 1 ≤ √((j:ℝ)+1) := by
      nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg ((j:ℝ)+1)]
    have hsq : (j:ℝ)+1 = (√((j:ℝ)+1))^2 := (Real.sq_sqrt hx0.le).symm
    have hL1 : Real.log ((j:ℝ)+1+1) - Real.log ((j:ℝ)+1) ≤ 1/((j:ℝ)+1) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((j:ℝ)+1+1)/((j:ℝ)+1) by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have e : ((j:ℝ)+1+1)/((j:ℝ)+1) - 1 = 1/((j:ℝ)+1) := by
        rw [div_sub_one hx0.ne']; ring
      linarith
    have hL2 : 1/((j:ℝ)+1+1) ≤ Real.log ((j:ℝ)+1+1) - Real.log ((j:ℝ)+1) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((j:ℝ)+1)/((j:ℝ)+1+1) by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have e : ((j:ℝ)+1)/((j:ℝ)+1+1) - 1 = -(1/((j:ℝ)+1+1)) := by
        rw [div_sub_one (by positivity)]; ring
      linarith
    have hwY : exp (-a (j+1)) * exp (a (j+1)) = 1 := by rw [mul_comm]; exact hYw (j+1)
    have hcore := core ((j:ℝ)+1) (√((j:ℝ)+1)) (exp (a (j+1))) (exp (-a (j+1)))
      (Real.log ((j:ℝ)+1+1) - Real.log ((j:ℝ)+1)) hs1 hsq (by linarith) (by linarith)
      hwY (exp_pos _) hL2 hL1
    have hfin : 5 / (√((j:ℝ)+1))^3 = 5 * (1 / (((j:ℝ)+1) * √((j:ℝ)+1))) := by
      rw [show (√((j:ℝ)+1))^3 = ((j:ℝ)+1) * √((j:ℝ)+1) by
        rw [pow_succ, Real.sq_sqrt hx0.le]]
      ring
    have e : a (j+1) + exp (-a (j+1)) - Real.log ((j:ℝ)+1+1) - (a (j+1) - Real.log ((j:ℝ)+1))
        = exp (-a (j+1)) - (Real.log ((j:ℝ)+1+1) - Real.log ((j:ℝ)+1)) := by ring
    rw [e]
    exact le_trans hcore (le_of_eq hfin)
  have hcomp : Summable (fun j : ℕ => 5 * (1 / ((j+1:ℕ):ℝ)^((3:ℝ)/2))) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ) < 3/2))
    exact this.mul_left 5
  have hsumm : Summable D := Summable.of_norm_bounded hcomp hD
  have hT := hsumm.hasSum.tendsto_sum_nat
  simp only [hsum] at hT
  have hg : Filter.Tendsto g Filter.atTop (𝓝 (∑' i, D i + g 0)) := by
    have := hT.add_const (g 0)
    simp only [sub_add_cancel] at this
    exact this
  exact ⟨∑' i, D i + g 0, (Filter.tendsto_add_atTop_iff_nat 1).mp (hg.congr (fun k => hg_def k))⟩
