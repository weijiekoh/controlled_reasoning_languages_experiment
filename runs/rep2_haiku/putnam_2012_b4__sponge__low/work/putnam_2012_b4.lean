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
  have hfac : ∀ n, exp (a n) * exp (-a n) = 1 := fun n => by rw [← exp_add]; simp
  have hsucc : ∀ n, exp (a (n+1)) = exp (a n) * exp (exp (-a n)) := fun n => by
    rw [han, exp_add]
  have hge : ∀ n : ℕ, (n:ℝ) + 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero =>
      have h1 : (1:ℝ) ≤ exp 1 := by have := add_one_le_exp (1:ℝ); linarith
      rw [ha0]; push_cast; linarith
    | succ k ih =>
      rw [hsucc k]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left (add_one_le_exp (exp (-a k))) (exp_pos (a k)).le,
        hfac k, ih]
  have ht1 : ∀ n : ℕ, exp (-a n) ≤ 1 / ((n:ℝ) + 1) := by
    intro n
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hfac n, hge n, exp_pos (-a n), mul_nonneg (exp_pos (-a n)).le
      (sub_nonneg.mpr (hge n))]
  have ht_le1 : ∀ n : ℕ, exp (-a n) ≤ 1 := by
    intro n
    have h := ht1 n
    have h2 : (1:ℝ) / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    linarith
  have hu : ∀ n : ℕ, |exp (a (n+1)) - exp (a n) - 1| ≤ 1 / ((n:ℝ) + 1) := by
    intro n
    have hb := abs_exp_sub_one_sub_id_le
      (abs_le.mpr ⟨by linarith [exp_pos (-a n)], ht_le1 n⟩)
    have heq : exp (a (n+1)) - exp (a n) - 1
        = exp (a n) * (exp (exp (-a n)) - 1 - exp (-a n)) := by
      rw [hsucc n]; linear_combination hfac n
    rw [heq, abs_mul, abs_of_pos (exp_pos _)]
    have h2 := mul_le_mul_of_nonneg_left hb (exp_pos (a n)).le
    have h3 : exp (a n) * (exp (-a n))^2 = exp (-a n) := by
      linear_combination (exp (-a n)) * hfac n
    linarith [ht1 n]
  have h0 : Tendsto (fun n : ℕ => exp (a (n+1)) - exp (a n) - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hu n)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => exp (a (n+1)) - exp (a n)) atTop (𝓝 1) := by
    have h1 := h0.add_const 1
    simp only [sub_add_cancel, zero_add] at h1
    exact h1
  have hC := hlim.cesaro
  have hS : ∀ n : ℕ, ∑ i ∈ Finset.range n, (exp (a (i+1)) - exp (a i))
      = exp (a n) - exp (a 0) := fun n => Finset.sum_range_sub (fun i => exp (a i)) n
  have hC' : Tendsto (fun n : ℕ => (n:ℝ)⁻¹ * (exp (a n) - exp (a 0))) atTop (𝓝 1) :=
    Tendsto.congr (fun n => by simp only [hS]) hC
  have hD : Tendsto (fun n : ℕ => exp (a n) / n) atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := hC'.add (hinv.const_mul (exp (a 0)))
    rw [mul_zero, add_zero] at this
    refine Tendsto.congr (fun n => ?_) this
    simp only [div_eq_mul_inv]; ring
  have hL : Tendsto (fun n : ℕ => Real.log (exp (a n) / n)) atTop
      (𝓝 (Real.log 1)) :=
    (Real.continuousAt_log one_ne_zero).tendsto.comp hD
  rw [Real.log_one] at hL
  have key : ∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L) := by
    refine ⟨0, Tendsto.congr' ?_ hL⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Real.log_div (exp_pos _).ne' hn0, Real.log_exp]
  refine ⟨fun _ => ?_, fun _ => key⟩
  exact trivial
