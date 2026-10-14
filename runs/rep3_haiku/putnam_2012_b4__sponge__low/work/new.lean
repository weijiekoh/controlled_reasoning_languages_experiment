import Mathlib

open Matrix Function Real Topology Filter

noncomputable abbrev putnam_2012_b4_solution : Prop := True
/--
Suppose that $a_0 = 1$ and that $a_{n+1} = a_n + e^{-a_n}$ for $n=0,1,2,\dots$. Does $a_n - \log n$
have a finite limit as $n \to \infty$? (Here $\log n = \log_e n = \ln n$.)
-/
by
  have hb : ∀ n : ℕ, (n : ℝ) + 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_add, ha0]
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    | succ k ih =>
      have h1 := Real.add_one_le_exp (exp (-a k))
      have hpos : 0 < exp (a k) := Real.exp_pos _
      have h2 : exp (a k) * (exp (-a k) + 1) ≤ exp (a k) * exp (exp (-a k)) :=
        mul_le_mul_of_nonneg_left h1 hpos.le
      have h3 : exp (a k) * exp (-a k) = 1 := by
        rw [← Real.exp_add]; simp
      have h4 : a (k+1) = a k + exp (-a k) := han k
      rw [h4, Real.exp_add]
      push_cast
      nlinarith
  set s : ℕ → ℝ := fun n => a (n + 1) - Real.log ((n + 1 : ℕ) : ℝ) with hs
  have hstep : ∀ n : ℕ, s (n + 1) ≤ s n := by
    intro n
    simp only [hs]
    have hA : a (n + 1 + 1) = a (n+1) + exp (-a (n+1)) := han (n+1)
    have hexp : exp (-a (n+1)) ≤ ((n:ℝ) + 1 + 1)⁻¹ := by
      rw [Real.exp_neg]
      apply inv_anti₀ (by positivity)
      have := hb (n+1)
      push_cast at this
      linarith
    have hlog : ((n:ℝ) + 1 + 1)⁻¹ ≤ Real.log ((n:ℝ) + 1 + 1) - Real.log ((n:ℝ) + 1) := by
      have hq : (0:ℝ) < ((n:ℝ) + 1 + 1) / ((n:ℝ) + 1) := by positivity
      have := Real.one_sub_inv_le_log_of_pos hq
      rw [Real.log_div (by positivity) (by positivity)] at this
      have e : 1 - (((n:ℝ) + 1 + 1) / ((n:ℝ) + 1))⁻¹ = ((n:ℝ) + 1 + 1)⁻¹ := by
        field_simp
        ring
      linarith
    push_cast
    rw [hA]
    linarith
  have hlow : ∀ n : ℕ, 0 ≤ s n := by
    intro n
    simp only [hs]
    have hn : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have := (Real.log_le_iff_le_exp hn).mpr (by have := hb (n+1); push_cast at this ⊢; linarith)
    linarith
  have hanti : Antitone s := antitone_nat_of_succ_le hstep
  have hbdd : BddBelow (Set.range s) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hlow n⟩
  have hT := tendsto_atTop_ciInf hanti hbdd
  have key : Tendsto (fun n => a n - Real.log (n : ℝ)) atTop (𝓝 (⨅ i, s i)) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mp hT
  exact ⟨fun _ => trivial, fun _ => ⟨_, key⟩⟩
