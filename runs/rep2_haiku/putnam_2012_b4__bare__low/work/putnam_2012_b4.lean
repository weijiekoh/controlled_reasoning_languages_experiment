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
  have hrec : ∀ n : ℕ, exp (a (n+1)) = exp (a n) * exp (1 / exp (a n)) := by
    intro n; rw [han n, Real.exp_add, Real.exp_neg, one_div]
  have hlow : ∀ n : ℕ, (n:ℝ) + 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      simp only [Nat.cast_zero, zero_add]
      linarith [Real.add_one_le_exp (1:ℝ)]
    | succ k ih =>
      rw [hrec k]
      have hx : 0 < exp (a k) := exp_pos _
      have h1 := Real.add_one_le_exp (1 / exp (a k))
      have h2 : exp (a k) * (1 + 1 / exp (a k)) = exp (a k) + 1 := by
        field_simp
      have h3 := mul_le_mul_of_nonneg_left h1 hx.le
      push_cast
      linarith
  have hup : ∀ n : ℕ, exp (a (n+1)) ≤ exp (a n) + 1 + 1 / exp (a n) := by
    intro n
    have hx1 : (1:ℝ) ≤ exp (a n) := by
      have := hlow n
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hx : 0 < exp (a n) := by linarith
    have hy0 : 0 ≤ 1 / exp (a n) := by positivity
    have hy1 : 1 / exp (a n) ≤ 1 := by rw [div_le_one hx]; exact hx1
    have hb := Real.abs_exp_sub_one_sub_id_le (x := 1 / exp (a n))
      (by rw [abs_of_nonneg hy0]; exact hy1)
    rw [abs_le] at hb
    have h4 : exp (1 / exp (a n)) ≤ 1 + 1 / exp (a n) + (1 / exp (a n))^2 := by
      linarith [hb.2]
    rw [hrec n]
    have h5 := mul_le_mul_of_nonneg_left h4 hx.le
    have h6 : exp (a n) * (1 + 1 / exp (a n) + (1 / exp (a n))^2)
        = exp (a n) + 1 + 1 / exp (a n) := by
      field_simp
    linarith
  have hlogsq : ∀ y : ℝ, 0 < y → Real.log y ≤ 2 * √y := by
    intro y hy
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
    rw [Real.log_sqrt hy.le] at h
    linarith [Real.sqrt_nonneg y]
  have hd : ∀ n : ℕ, exp (a n) - n ≤ 3 + 2 * Real.log ((n:ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      simp only [Nat.cast_zero, zero_add, Real.log_one, mul_zero, add_zero, sub_zero]
      linarith [Real.exp_one_lt_d9]
    | succ k ih =>
      have hu := hup k
      have hinv : 1 / exp (a k) ≤ 1 / ((k:ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (hlow k)
      have hlog : 1 / ((k:ℝ) + 1 + 1) ≤ Real.log ((k:ℝ) + 1 + 1) - Real.log ((k:ℝ) + 1) := by
        have h := Real.one_sub_inv_le_log_of_pos
          (x := ((k:ℝ) + 1 + 1) / ((k:ℝ) + 1)) (by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h
        have e : 1 - (((k:ℝ) + 1 + 1) / ((k:ℝ) + 1))⁻¹ = 1 / ((k:ℝ) + 1 + 1) := by
          rw [inv_div]
          field_simp
          ring
        linarith
      have hk := Nat.cast_nonneg (α := ℝ) k
      have h7 : 1 / ((k:ℝ) + 1) ≤ 2 * (1 / ((k:ℝ) + 1 + 1)) := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      push_cast
      linarith
  have hdsq : ∀ n : ℕ, exp (a n) - n ≤ 3 + 4 * √((n:ℝ) + 1) := by
    intro n
    have := hd n
    have h := hlogsq ((n:ℝ) + 1) (by positivity)
    linarith
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |(a (n+1) - Real.log ((n:ℝ) + 1)) - (a n - Real.log n)|
        ≤ 12 * (1 / ((n:ℝ) * √(n:ℝ))) := by
    intro n hn
    have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hNpos : (0:ℝ) < n := by linarith
    have hs1 : 1 ≤ √(n:ℝ) := by
      rw [show (1:ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hN
    have hs : 0 < √(n:ℝ) := by linarith
    have hss : √(n:ℝ)^2 = n := Real.sq_sqrt hNpos.le
    have hsN : √(n:ℝ) ≤ n := by nlinarith
    have hxn : (n:ℝ) ≤ exp (a n) := by linarith [hlow n]
    have hx : 0 < exp (a n) := by linarith
    have hdn := hdsq n
    have hs2 : √((n:ℝ)+1) ≤ 2 * √(n:ℝ) := by
      nlinarith [Real.sqrt_nonneg ((n:ℝ)+1), Real.sq_sqrt (show (0:ℝ) ≤ (n:ℝ)+1 by positivity)]
    have hdn2 : exp (a n) - n ≤ 11 * √(n:ℝ) := by linarith
    -- the log difference
    have hL1 : 1 / ((n:ℝ) + 1) ≤ Real.log ((n:ℝ) + 1) - Real.log n := by
      have h := Real.one_sub_inv_le_log_of_pos
        (x := ((n:ℝ) + 1) / (n:ℝ)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have e : 1 - (((n:ℝ) + 1) / (n:ℝ))⁻¹ = 1 / ((n:ℝ) + 1) := by
        rw [inv_div]
        field_simp
        ring
      linarith
    have hL2 : Real.log ((n:ℝ) + 1) - Real.log n ≤ 1 / (n:ℝ) := by
      have h := Real.log_le_sub_one_of_pos (x := ((n:ℝ) + 1) / (n:ℝ)) (by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      have e : ((n:ℝ) + 1) / (n:ℝ) - 1 = 1 / (n:ℝ) := by
        field_simp
        ring
      linarith
    have hinv : 1 / exp (a n) ≤ 1 / (n:ℝ) := one_div_le_one_div_of_le hNpos hxn
    have hstep : a (n+1) = a n + 1 / exp (a n) := by
      rw [han n, Real.exp_neg, one_div]
    have e1 : 1 / (n:ℝ) - 1 / exp (a n) = (exp (a n) - n) / (n * exp (a n)) := by
      field_simp
    have e2 : (exp (a n) - n) / (n * exp (a n)) ≤ (exp (a n) - n) / (n * n) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity)
        (mul_le_mul_of_nonneg_left hxn hNpos.le)
    have e3 : (exp (a n) - n) / ((n:ℝ) * n) ≤ 11 * (1 / ((n:ℝ) * √(n:ℝ))) := by
      have e4 : (1:ℝ) / ((n:ℝ) * √(n:ℝ)) = √(n:ℝ) / ((n:ℝ) * n) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linear_combination (-(n:ℝ)) * hss
      rw [e4, mul_div_assoc']
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have e5 : 1 / (n:ℝ) - 1 / ((n:ℝ) + 1) ≤ 1 / ((n:ℝ) * n) := by
      rw [div_sub_div _ _ hNpos.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e6 : 1 / ((n:ℝ) * n) ≤ 1 / ((n:ℝ) * √(n:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hsN hNpos.le)
    have hg : 0 ≤ 1 / ((n:ℝ) * √(n:ℝ)) := by positivity
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hcauchy : CauchySeq (fun n : ℕ => a n - Real.log n) := by
    apply cauchySeq_of_summable_dist
    have hg : Summable (fun n : ℕ => 12 * (1 / ((n:ℝ) * √(n:ℝ)))) := by
      apply Summable.mul_left
      have hfun : (fun n : ℕ => 1 / ((n:ℝ) * √(n:ℝ)))
          = fun n : ℕ => 1 / (n:ℝ) ^ (3/2 : ℝ) := by
        funext n
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · have hp : (0:ℝ) < n := by exact_mod_cast h
          rw [show (3/2:ℝ) = 1/2 + 1 by norm_num, Real.rpow_add hp, Real.rpow_one,
            Real.sqrt_eq_rpow]; ring
      rw [hfun]
      exact Real.summable_one_div_nat_rpow.mpr (by norm_num)
    apply Summable.of_norm_bounded_eventually hg
    have h1 : ∀ᶠ n : ℕ in Filter.cofinite, 1 ≤ n := by
      rw [Nat.cofinite_eq_atTop]
      exact eventually_ge_atTop 1
    filter_upwards [h1] with n hn
    rw [Real.norm_of_nonneg dist_nonneg, Real.dist_eq, abs_sub_comm]
    have := hbound n hn
    push_cast
    linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨fun _ => trivial, fun _ => ⟨L, hL⟩⟩
