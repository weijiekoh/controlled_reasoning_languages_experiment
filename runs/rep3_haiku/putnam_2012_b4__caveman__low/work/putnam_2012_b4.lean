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
: ((∃ L : ℝ, Tendsto (fun n ↦ a n - Real.log n) atTop (𝓝 L)) ↔ putnam_2012_b4_solution) :=
by
  have hE : ∀ n : ℕ, (n:ℝ) + 1 ≤ exp (a n) := by
    intro n
    induction n with
    | zero =>
      rw [ha0]
      push_cast
      linarith [add_one_le_exp (1:ℝ)]
    | succ k ih =>
      rw [han k, exp_add]
      have h1 : exp (-a k) * exp (a k) = 1 := by rw [← exp_add]; simp
      have h2 := add_one_le_exp (exp (-a k))
      have h3 := mul_le_mul_of_nonneg_left h2 (exp_pos (a k)).le
      have h4 : exp (a k) * (1 + exp (-a k)) = exp (a k) + 1 := by
        linear_combination h1
      push_cast
      linarith
  have hstep : ∀ m : ℕ, 1 ≤ m → exp (-a m) ≤ log ((m:ℝ)+1) - log m := by
    intro m hm
    have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hpos : (0:ℝ) < m := by linarith
    have hl := Real.one_sub_inv_le_log_of_pos (x := ((m:ℝ)+1)/m) (by positivity)
    rw [Real.log_div (by positivity) hpos.ne'] at hl
    have hinv : (1:ℝ) - (((m:ℝ)+1)/m)⁻¹ = 1/((m:ℝ)+1) := by
      field_simp <;> ring_nf
    have hE' := hE m
    have hb : exp (-a m) ≤ 1/((m:ℝ)+1) := by
      rw [exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) hE'
    linarith
  have hmono : ∀ n : ℕ, a (n+1+1) - log (((n+1+1 : ℕ)) : ℝ) ≤ a (n+1) - log ((n+1 : ℕ):ℝ) := by
    intro n
    have h := hstep (n+1) (by omega)
    rw [han (n+1)]
    push_cast at h ⊢
    linarith
  have hanti : Antitone (fun n : ℕ => a (n+1) - log ((n+1:ℕ):ℝ)) :=
    antitone_nat_of_succ_le (fun n => hmono n)
  have hbdd : BddBelow (Set.range fun n : ℕ => a (n+1) - log ((n+1:ℕ):ℝ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    show 0 ≤ a (n+1) - log ((n+1:ℕ):ℝ)
    have h1 := Real.log_le_log (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ))
      (show ((n+1:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ)+1 by linarith)
    have h2 := Real.log_le_log (by positivity) (hE (n+1))
    rw [log_exp] at h2
    linarith
  have hlim := tendsto_atTop_ciInf hanti hbdd
  have hfin : Tendsto (fun n : ℕ => a n - log (n:ℝ)) atTop
      (𝓝 (⨅ n : ℕ, (a (n+1) - log ((n+1:ℕ):ℝ)))) :=
    (tendsto_add_atTop_iff_nat 1).mp hlim
  exact ⟨fun _ => trivial, fun _ => ⟨_, hfin⟩⟩
