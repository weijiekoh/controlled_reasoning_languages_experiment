import Mathlib

lemma aux_rat (N D : ℤ) (hD : D ≠ 0) (hc : IsCoprime N D) :
    ((N:ℚ)/(D:ℚ)).num.natAbs + ((N:ℚ)/(D:ℚ)).den = N.natAbs + D.natAbs := by
  have hcop : Nat.Coprime N.natAbs D.natAbs := Int.isCoprime_iff_gcd_eq_one.mp hc
  rcases lt_or_gt_of_ne hD with h | h
  · have e : (N:ℚ)/(D:ℚ) = ((-N:ℤ):ℚ)/((-D:ℤ):ℚ) := by push_cast; rw [neg_div_neg_eq]
    have hcop' : Nat.Coprime (-N).natAbs (-D).natAbs := by simpa [Int.natAbs_neg] using hcop
    have h1 := Rat.num_div_eq_of_coprime (a := -N) (b := -D) (by omega) hcop'
    have h2 := Rat.den_div_eq_of_coprime (a := -N) (b := -D) (by omega) hcop'
    rw [e, h1]
    have h3 : (((-N:ℤ):ℚ)/((-D:ℤ):ℚ)).den = (-D).natAbs := by
      have := h2; omega
    rw [h3, Int.natAbs_neg, Int.natAbs_neg]
  · have h1 := Rat.num_div_eq_of_coprime (a := N) (b := D) h hcop
    have h2 := Rat.den_div_eq_of_coprime (a := N) (b := D) h hcop
    rw [h1]
    have h3 : ((N:ℚ)/(D:ℚ)).den = D.natAbs := by
      have := h2; omega
    rw [h3]

lemma key_pq (x : ℚ) (p q : ℤ) (hq : 0 < q) (hx : x = (p:ℚ)/(q:ℚ)) (hc : IsCoprime p q)
    (hp : p ≠ 0) (hx2 : x^2 ≠ 1) :
    p.natAbs + q.natAbs + 1 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
  subst hx
  have hp' : (p:ℚ) ≠ 0 := by exact_mod_cast hp
  have hq' : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsq : p^2 ≠ q^2 := by
    intro h; apply hx2
    have : (p:ℚ)^2 = (q:ℚ)^2 := by exact_mod_cast h
    rw [div_pow, this, div_self (pow_ne_zero _ hq')]
  have hD : (p:ℚ)/(q:ℚ) - 1/((p:ℚ)/(q:ℚ)) = ((p^2-q^2 : ℤ):ℚ)/((p*q : ℤ):ℚ) := by
    push_cast; field_simp
  have hDne : p*q ≠ 0 := mul_ne_zero hp hq.ne'
  have hc1 : IsCoprime (p^2-q^2) p := by
    have h1 : IsCoprime (-(q^2)) p := (hc.symm.pow_left (m := 2)).neg_left
    have e : p^2 - q^2 = -(q^2) + p*p := by ring
    rw [e]; exact h1.add_mul_left_left p
  have hc2 : IsCoprime (p^2-q^2) q := by
    have h1 : IsCoprime (p^2) q := hc.pow_left
    have e : p^2 - q^2 = p^2 + q*(-q) := by ring
    rw [e]; exact h1.add_mul_left_left (-q)
  have hc3 : IsCoprime (p^2-q^2) (p*q) := hc1.mul_right hc2
  rw [hD, aux_rat _ _ hDne hc3, Int.natAbs_mul]
  have hA : ((p.natAbs:ℕ):ℤ)^2 = p^2 := Int.natAbs_sq p
  have hB : ((q.natAbs:ℕ):ℤ)^2 = q^2 := Int.natAbs_sq q
  have hAB : (p.natAbs:ℤ) ≠ (q.natAbs:ℤ) := by
    intro h; apply hsq; rw [← hA, ← hB, h]
  have hpa : 1 ≤ p.natAbs := Int.natAbs_pos.mpr hp
  have hqa : 1 ≤ q.natAbs := by omega
  have hN : p.natAbs + q.natAbs ≤ (p^2-q^2).natAbs := by
    have e : p^2 - q^2 = ((p.natAbs:ℕ):ℤ)^2 - ((q.natAbs:ℕ):ℤ)^2 := by rw [hA, hB]
    rw [e]
    rcases lt_or_gt_of_ne hAB with h | h
    · have : ((p.natAbs:ℕ):ℤ)^2 - ((q.natAbs:ℕ):ℤ)^2 ≤ -((p.natAbs:ℤ)+(q.natAbs:ℤ)) := by
        nlinarith
      omega
    · have : ((p.natAbs:ℕ):ℤ)^2 - ((q.natAbs:ℕ):ℤ)^2 ≥ ((p.natAbs:ℤ)+(q.natAbs:ℤ)) := by
        nlinarith
      omega
  have hM : 1 ≤ p.natAbs * q.natAbs := Nat.one_le_iff_ne_zero.mpr (by positivity)
  omega
