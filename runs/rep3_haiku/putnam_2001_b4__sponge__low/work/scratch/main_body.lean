
theorem putnam_2001_b4
(S : Set ℚ)
(hS : S = univ \ {-1, 0, 1})
(f : S → S)
(hf : ∀ x : S, f x = x - 1 / (x : ℚ))
: ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ ↔ putnam_2001_b4_solution := by
  have hS' : ∀ x : S, (x:ℚ) ≠ 0 ∧ (x:ℚ)^2 ≠ 1 := by
    intro x
    have hx := x.2
    rw [hS] at hx
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, mem_univ, true_and, not_or] at hx
    obtain ⟨h1, h0, h2⟩ := hx
    refine ⟨h0, ?_⟩
    intro h
    rcases mul_eq_zero.mp (show ((x:ℚ)-1)*((x:ℚ)+1) = 0 by linear_combination h) with h' | h'
    · exact h2 (by linarith)
    · exact h1 (by linarith)
  have hstep : ∀ x : S, x.1.num.natAbs + x.1.den + 1 ≤ ((f x : S):ℚ).num.natAbs + ((f x : S):ℚ).den := by
    intro x
    have hfx : ((f x : S):ℚ) = (x:ℚ) - 1/(x:ℚ) := by rw [hf]
    rw [hfx]
    obtain ⟨h0, h2⟩ := hS' x
    have hq : (0:ℤ) < ((x.1.den:ℕ):ℤ) := by exact_mod_cast x.1.den_pos
    have hxe : (x:ℚ) = (x.1.num:ℚ)/(((x.1.den:ℕ):ℤ):ℚ) := by
      rw [Int.cast_natCast, Rat.num_div_den]
    have hc : IsCoprime x.1.num ((x.1.den:ℕ):ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr x.1.reduced
    have hp : x.1.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have := key_pq (x:ℚ) x.1.num ((x.1.den:ℕ):ℤ) hq hxe hc hp h2
    have e : ((x.1.den:ℕ):ℤ).natAbs = x.1.den := rfl
    rw [e] at this
    exact this
  have hiter : ∀ n : ℕ, ∀ x : S, x.1.num.natAbs + x.1.den + n ≤ ((f^[n] x : S):ℚ).num.natAbs + ((f^[n] x : S):ℚ).den := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply]
      have h1 := ih (f x)
      have h2 := hstep x
      omega
  refine iff_of_true ?_ trivial
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro y hy
  simp only [mem_iInter, mem_image, mem_univ, true_and, mem_Ici] at hy
  obtain ⟨x, hx⟩ := hy (y.1.num.natAbs + y.1.den + 1) (by omega)
  have := hiter (y.1.num.natAbs + y.1.den + 1) x
  rw [hx] at this
  omega
