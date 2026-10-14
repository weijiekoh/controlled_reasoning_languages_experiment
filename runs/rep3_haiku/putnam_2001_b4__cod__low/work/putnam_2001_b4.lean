import Mathlib

open Topology Filter Polynomial Set

noncomputable abbrev putnam_2001_b4_solution : Prop := True
/--
Let $S$ denote the set of rational numbers different from $\{-1,0,1\}$.  Define $f:S\rightarrow S$ by $f(x)=x-1/x$. Prove or disprove that \[\bigcap_{n=1}^\infty f^{(n)}(S) = \emptyset,\] where $f^{(n)}$ denotes $f$ composed with itself $n$ times.
-/
theorem putnam_2001_b4
(S : Set ℚ)
(hS : S = univ \ {-1, 0, 1})
(f : S → S)
(hf : ∀ x : S, f x = x - 1 / (x : ℚ))
: ⋂ n ∈ Ici 1, f^[n] '' univ = ∅ ↔ putnam_2001_b4_solution :=by
  -- height function
  set H : ℚ → ℕ := fun q => q.num.natAbs + q.den with hH
  have L : ∀ c d : ℤ, d ≠ 0 → Nat.Coprime c.natAbs d.natAbs →
      H ((c:ℚ)/(d:ℚ)) = c.natAbs + d.natAbs := by
    have pos : ∀ c d : ℤ, 0 < d → Nat.Coprime c.natAbs d.natAbs →
        H ((c:ℚ)/(d:ℚ)) = c.natAbs + d.natAbs := by
      intro c d hd h
      have hn := Rat.num_div_eq_of_coprime hd h
      have hd' := Rat.den_div_eq_of_coprime hd h
      simp only [hH]
      rw [hn]
      have : ((c:ℚ)/(d:ℚ)).den = d.natAbs := by
        have := hd'
        omega
      rw [this]
    intro c d hd h
    rcases lt_or_gt_of_ne hd with hd | hd
    · have e : (c:ℚ)/(d:ℚ) = ((-c:ℤ):ℚ)/((-d:ℤ):ℚ) := by
        push_cast; rw [neg_div_neg_eq]
      rw [e, pos (-c) (-d) (by omega)]
      · simp [Int.natAbs_neg]
      · simpa [Int.natAbs_neg] using h
    · exact pos c d hd h
  have step : ∀ x : ℚ, x ∈ (univ \ {-1, 0, 1} : Set ℚ) →
      H (x - 1/x) ≥ H x + 1 := by
    intro x hx
    simp only [Set.mem_sdiff, mem_univ, true_and, mem_insert_iff, mem_singleton_iff, not_or] at hx
    obtain ⟨h2, h0, h1⟩ := hx
    have hanz : x.num ≠ 0 := Rat.num_ne_zero.mpr h0
    have hb : (0:ℤ) < (x.den:ℤ) := by exact_mod_cast x.den_pos
    have hab : IsCoprime x.num (x.den:ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have := x.reduced
      simpa [Int.gcd] using this
    have hxe : x = (x.num:ℚ)/((x.den:ℤ):ℚ) := by
      push_cast; exact (Rat.num_div_den x).symm
    set a := x.num with ha
    set b : ℤ := (x.den:ℤ) with hb'
    have hcop : IsCoprime (a^2 - b^2) (a*b) := by
      apply IsCoprime.mul_right
      · have e : a^2 - b^2 = -(b^2) + a*a := by ring
        rw [e]
        exact IsCoprime.add_mul_left_left (hab.symm.pow_left).neg_left a
      · have e : a^2 - b^2 = a^2 + b*(-b) := by ring
        rw [e]
        exact IsCoprime.add_mul_left_left (hab.pow_left) (-b)
    have hcop' : Nat.Coprime (a^2 - b^2).natAbs (a*b).natAbs :=
      Int.isCoprime_iff_gcd_eq_one.mp hcop
    have hb0 : b ≠ 0 := ne_of_gt hb
    have hab0 : a*b ≠ 0 := mul_ne_zero hanz hb0
    have hval : x - 1/x = ((a^2-b^2 : ℤ):ℚ)/((a*b : ℤ):ℚ) := by
      have hx0 : x ≠ 0 := h0
      have hbq : ((b:ℤ):ℚ) ≠ 0 := by exact_mod_cast hb0
      have haq : ((a:ℤ):ℚ) ≠ 0 := by exact_mod_cast hanz
      conv_lhs => rw [hxe]
      field_simp
      push_cast
      ring
    have hLx := L (a^2-b^2) (a*b) hab0 hcop'
    rw [hval, hLx]
    have hz0 : (a * b).natAbs = a.natAbs * b.natAbs := Int.natAbs_mul a b
    rw [hz0]
    have hHx : H x = a.natAbs + b.natAbs := by
      rw [hH]
      simp [ha, hb']
    rw [hHx]
    -- integer inequality
    have hAB : a.natAbs ≠ b.natAbs := by
      intro heq
      have hb1 : b.natAbs = (x.den) := by simp [hb']
      -- coprime with equal abs values forces both = 1
      have hcp : Nat.Coprime a.natAbs b.natAbs := by
        have := hab
        rw [Int.isCoprime_iff_gcd_eq_one] at this
        simpa [Int.gcd] using this
      rw [heq] at hcp
      have h1' : b.natAbs = 1 := by
        unfold Nat.Coprime at hcp
        simpa using hcp
      have ha1 : a.natAbs = 1 := heq.trans h1'
      have hb1' : b = 1 := by omega
      have ha' : a = 1 ∨ a = -1 := by omega
      have hxv : x = 1 ∨ x = -1 := by
        rcases ha' with ha' | ha'
        · left; rw [hxe, ha', hb1']; norm_num
        · right; rw [hxe, ha', hb1']; norm_num
      exact (hxv.elim h1 h2)
    have hA1 : 1 ≤ a.natAbs := by omega
    have hB1 : 1 ≤ b.natAbs := by
      have : b.natAbs = x.den := by simp [hb']
      have := x.den_pos
      omega
    have ea : ((a^2-b^2).natAbs : ℤ) = |a^2 - b^2| := by simp
    have hz : ((a*b).natAbs) = a.natAbs * b.natAbs := Int.natAbs_mul a b
    -- reduce to natural/int inequality on A=|a|, B=|b|
    have key : ∀ A B : ℤ, 1 ≤ A → 1 ≤ B → A ≠ B →
        A + B + 1 ≤ |A^2 - B^2| + A*B := by
      intro A B hA hB hne
      have hAB1 : 1 ≤ A * B := by nlinarith
      rcases lt_or_gt_of_ne hne with h | h
      · have e : |A^2 - B^2| = B^2 - A^2 := by
          rw [abs_of_nonpos (show A^2 - B^2 ≤ 0 by nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ B - A) (by omega : (0:ℤ) ≤ A + B)])]
          ring
        rw [e]
        have h4 : (B - A) * (A + B) ≥ 1 * (A + B) := mul_le_mul_of_nonneg_right (by omega) (by omega)
        nlinarith
      · have e : |A^2 - B^2| = A^2 - B^2 := by
          rw [abs_of_nonneg (show 0 ≤ A^2 - B^2 by nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ A - B) (by omega : (0:ℤ) ≤ A + B)])]
        rw [e]
        have h4 : (A - B) * (A + B) ≥ 1 * (A + B) := mul_le_mul_of_nonneg_right (by omega) (by omega)
        nlinarith
    have hk := key (a.natAbs:ℤ) (b.natAbs:ℤ) (by omega) (by omega)
      (by exact_mod_cast hAB)
    have hsq : ((a.natAbs:ℤ))^2 - ((b.natAbs:ℤ))^2 = (a^2 - b^2) := by
      simp [sq_abs]
    have hs2 : |a^2 - b^2| = ((a^2-b^2).natAbs : ℤ) := by simp
    rw [hsq, hs2] at hk
    have hfin : ((a^2-b^2).natAbs : ℤ) + (a.natAbs:ℤ) * (b.natAbs:ℤ) ≥ (a.natAbs:ℤ) + (b.natAbs:ℤ) + 1 := by
      linarith [hk]
    have hA' : (a.natAbs:ℤ) + (b.natAbs:ℤ) + 1 ≤ ((a^2-b^2).natAbs : ℤ) + (a.natAbs:ℤ) * (b.natAbs:ℤ) := hfin
    omega
  subst hS
  simp only [putnam_2001_b4_solution, iff_true]
  have iter : ∀ n : ℕ, ∀ x : (univ \ {-1, 0, 1} : Set ℚ),
      H (x : ℚ) + n ≤ H (((f^[n] x) : (univ \ {-1, 0, 1} : Set ℚ)) : ℚ) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      have hs := step (((f^[n] x) : (univ \ {-1, 0, 1} : Set ℚ)) : ℚ) (f^[n] x).2
      rw [hf]
      have := ih x
      omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨x, _, hx⟩ := (mem_iInter₂.mp hz) (H (z : ℚ) + 1) (Set.mem_Ici.mpr (by omega))
  have := iter (H (z : ℚ) + 1) x
  rw [hx] at this
  omega
