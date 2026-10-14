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
  have hA : ∀ n : ℕ, (n:ℝ) + 2 ≤ exp (a n) := by
    intro n
    induction n with
    | zero => rw [ha0]; push_cast; linarith [Real.add_one_le_exp 1]
    | succ k ih =>
      have h1 := Real.add_one_le_exp (exp (-a k))
      have h2 : exp (a k) * (exp (-a k) + 1) ≤ exp (a k) * exp (exp (-a k)) :=
        mul_le_mul_of_nonneg_left h1 (exp_pos _).le
      have hu : exp (a k) * exp (-a k) = 1 := by rw [← exp_add]; simp
      rw [han k, exp_add]
      push_cast
      nlinarith
  have hu_bound : ∀ u : ℝ, 0 ≤ u → u ≤ 1/2 → exp u ≤ 1 + u + 2*u^2 := by
    intro u h0 h1
    have h2 : 1 - u ≤ exp (-u) := by linarith [Real.add_one_le_exp (-u)]
    have h3 : exp u * exp (-u) = 1 := by rw [← exp_add]; simp
    have h4 : exp u * (1 - u) ≤ 1 := by nlinarith [exp_pos u]
    have h5 : (0:ℝ) < 1 - u := by linarith
    nlinarith [exp_pos u, mul_nonneg (sq_nonneg u) (by linarith : (0:ℝ) ≤ 1 - 2*u)]
  have hB : ∀ n : ℕ, exp (a n) ≤ (n:ℝ) + 4 * √(n:ℝ) + 3 := by
    intro n
    induction n with
    | zero =>
      have h := Real.exp_one_lt_d9
      simp only [Nat.cast_zero, ha0, Real.sqrt_zero]
      norm_num
      linarith
    | succ k ih =>
      have hx := hA k
      have hxu : exp (a k) * exp (-a k) = 1 := by rw [← exp_add]; simp
      have hu0 : 0 < exp (-a k) := exp_pos _
      have hE := hu_bound (exp (-a k)) hu0.le (by nlinarith [exp_pos (a k)])
      have hxpos : 0 < exp (a k) := exp_pos _
      have hstep : exp (a (k+1)) = exp (a k) * exp (exp (-a k)) := by rw [han k, exp_add]
      rw [hstep]
      have h5 : exp (a k) * exp (exp (-a k)) ≤ exp (a k) + 1 + 2 * exp (-a k) := by
        nlinarith [mul_le_mul_of_nonneg_left hE hxpos.le]
      have hs : √(k:ℝ) ^ 2 = k := sq_sqrt (Nat.cast_nonneg k)
      have ht : √((k:ℝ)+1) ^ 2 = (k:ℝ) + 1 := sq_sqrt (by positivity)
      have hts : √(k:ℝ) ≤ √((k:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
      have hs0 := Real.sqrt_nonneg (k:ℝ)
      have ht0 := Real.sqrt_nonneg ((k:ℝ)+1)
      have hst : √(k:ℝ) * √((k:ℝ)+1) ≤ k + 1/2 := by nlinarith [sq_nonneg (√((k:ℝ)+1) - √(k:ℝ))]
      have hxt : √((k:ℝ)+1) ≤ exp (a k) := by nlinarith
      have h6 : 2 ≤ 4 * (√((k:ℝ)+1) - √(k:ℝ)) * exp (a k) := by
        nlinarith [mul_le_mul_of_nonneg_left hxt (sub_nonneg.2 hts)]
      have h7 : 2 * exp (-a k) ≤ 4 * (√((k:ℝ)+1) - √(k:ℝ)) := by nlinarith
      push_cast
      linarith
  have hkey : ∀ n : ℕ, 1 ≤ n → |(a (n+1) - Real.log ((n+1:ℕ):ℝ)) - (a n - Real.log (n:ℝ))| ≤ 8 * ((n:ℝ)^(3/2:ℝ))⁻¹ := by
    intro n hn
    have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hNpos : (0:ℝ) < n := by linarith
    have hcast : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by push_cast; ring
    rw [hcast, han n]
    have hx := hA n
    have hxB := hB n
    have hxu : exp (a n) * exp (-a n) = 1 := by rw [← exp_add]; simp
    have hD : (a n + exp (-a n) - Real.log ((n:ℝ)+1)) - (a n - Real.log n)
        = exp (-a n) - (Real.log ((n:ℝ)+1) - Real.log n) := by ring
    rw [hD]
    have hL2 : Real.log ((n:ℝ)+1) - Real.log n ≤ 1/(n:ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ)+1)/n by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have : ((n:ℝ)+1)/n - 1 = 1/n := by field_simp; ring
      linarith
    have hL1 : 1/((n:ℝ)+1) ≤ Real.log ((n:ℝ)+1) - Real.log n := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (n:ℝ)/((n:ℝ)+1) by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have : (n:ℝ)/((n:ℝ)+1) - 1 = -(1/((n:ℝ)+1)) := by field_simp; ring
      linarith
    have hr : ((n:ℝ))^(3/2:ℝ) = n * √(n:ℝ) := by
      rw [Real.sqrt_eq_rpow, show (3/2:ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
    rw [hr]
    set x := exp (a n) with hxdef
    set u := exp (-a n) with hudef
    set s := √(n:ℝ) with hsdef
    have hs : s^2 = n := sq_sqrt hNpos.le
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; linarith
    have hs1 : 1 ≤ s := by nlinarith [Real.sqrt_nonneg (n:ℝ)]
    have hu0 : 0 < u := exp_pos _
    have hu_le : u ≤ 1/(n:ℝ) := by
      rw [le_div_iff₀ hNpos]; nlinarith
    have key2 : (n:ℝ) - n^2*u ≤ 4*s+3 := by
      have e : (n:ℝ) - n^2*u = (n*u)*(x - n) := by linear_combination (-(n:ℝ)) * hxu
      rw [e]
      have hnu : (n:ℝ)*u ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hnu (by linarith : (0:ℝ) ≤ x - n)]
    have hlow : 1/(n:ℝ) - u ≤ (4*s+3)/(n:ℝ)^2 := by
      have e1 : 1/(n:ℝ) - u = ((n:ℝ) - n^2*u)/(n:ℝ)^2 := by field_simp
      rw [e1]; exact div_le_div_of_nonneg_right key2 (by positivity)
    have e2 : (n*s)⁻¹ = s/(n:ℝ)^2 := by
      rw [show (n:ℝ) = s^2 from hs.symm]
      field_simp
    rw [e2]
    have h3 : 1/(n:ℝ) - 1/((n:ℝ)+1) ≤ 1/(n:ℝ)^2 := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h8 : 1/(n:ℝ)^2 ≤ 8*(s/(n:ℝ)^2) := by
      rw [← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); linarith
    have h4 : (4*s+3)/(n:ℝ)^2 ≤ 8*(s/(n:ℝ)^2) := by
      rw [← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity); linarith
    rw [abs_le]
    constructor
    · linarith [hL2, hlow, h4]
    · linarith [hu_le, hL1, h3, h8]
  have hbase : Summable (fun n:ℕ => 8 * ((n:ℝ)^(3/2:ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 8
  have hg : Summable (fun k:ℕ => 8 * (((k+1:ℕ):ℝ)^(3/2:ℝ))⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase
  have hS : Summable (fun i:ℕ => (a (i+1+1) - Real.log ((i+1+1:ℕ):ℝ)) - (a (i+1) - Real.log ((i+1:ℕ):ℝ))) := by
    refine Summable.of_norm_bounded hg ?_
    intro i
    rw [Real.norm_eq_abs]
    exact hkey (i+1) (by omega)
  have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((a (i+1+1) - Real.log ((i+1+1:ℕ):ℝ)) - (a (i+1) - Real.log ((i+1:ℕ):ℝ)))
      = (a (n+1) - Real.log ((n+1:ℕ):ℝ)) - (a 1 - Real.log ((1:ℕ):ℝ)) := by
    intro n
    have := Finset.sum_range_sub (fun i : ℕ => a (i+1) - Real.log ((i+1:ℕ):ℝ)) n
    simpa using this
  have hlim := HasSum.tendsto_sum_nat hS.hasSum
  rw [show (fun n:ℕ => ∑ i ∈ Finset.range n, ((a (i+1+1) - Real.log ((i+1+1:ℕ):ℝ)) - (a (i+1) - Real.log ((i+1:ℕ):ℝ)))) = fun n => (a (n+1) - Real.log ((n+1:ℕ):ℝ)) - (a 1 - Real.log ((1:ℕ):ℝ)) from funext htel] at hlim
  have hc1 : Tendsto (fun n:ℕ => (a (n+1) - Real.log ((n+1:ℕ):ℝ))) atTop
      (𝓝 (∑' i:ℕ, ((a (i+1+1) - Real.log ((i+1+1:ℕ):ℝ)) - (a (i+1) - Real.log ((i+1:ℕ):ℝ))) + (a 1 - Real.log ((1:ℕ):ℝ)))) := by
    have := hlim.add_const (a 1 - Real.log ((1:ℕ):ℝ))
    simpa using this
  have hc : Tendsto (fun n:ℕ => a n - Real.log (n:ℝ)) atTop
      (𝓝 (∑' i:ℕ, ((a (i+1+1) - Real.log ((i+1+1:ℕ):ℝ)) - (a (i+1) - Real.log ((i+1:ℕ):ℝ))) + (a 1 - Real.log ((1:ℕ):ℝ)))) :=
    (tendsto_add_atTop_iff_nat 1).mp hc1
  simp only [putnam_2012_b4_solution]
  exact ⟨fun _ => trivial, fun _ => ⟨_, hc⟩⟩
