import Mathlib
open Set

lemma nd_lemma (a b : ℤ) (hb : b ≠ 0) (h : IsCoprime a b) :
    ((a:ℚ)/(b:ℚ)).num.natAbs = a.natAbs ∧ (((a:ℚ)/(b:ℚ)).den : ℤ) = b.natAbs := by
  have hc : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · have e : (a:ℚ)/(b:ℚ) = (-a : ℤ)/(-b : ℤ) := by push_cast; rw [neg_div_neg_eq]
    rw [e, Rat.num_div_eq_of_coprime (by omega) (by simpa using hc),
      Rat.den_div_eq_of_coprime (by omega) (by simpa using hc)]
    constructor
    · omega
    · omega
  · rw [Rat.num_div_eq_of_coprime hpos hc, Rat.den_div_eq_of_coprime hpos hc]
    constructor
    · omega
    · omega

lemma ineq_lemma (a q : ℤ) (ha : 1 ≤ a) (hq : 1 ≤ q) (hne : a ≠ q) :
    a + q + 2 ≤ |a^2 - q^2| + a * q := by
  have h3 : 3 ≤ a + q := by omega
  have h2 : 2 ≤ a * q := by nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ a - 1) (by omega : (0:ℤ) ≤ q - 1)]
  rcases lt_or_gt_of_ne hne with h | h
  · have : a^2 - q^2 = -((q-a)*(q+a)) := by ring
    rw [this, abs_neg, abs_of_nonneg (by nlinarith)]
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ q - a - 1) (by omega : (0:ℤ) ≤ q + a)]
  · have : a^2 - q^2 = (a-q)*(a+q) := by ring
    rw [this, abs_of_nonneg (by nlinarith)]
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ a - q - 1) (by omega : (0:ℤ) ≤ q + a)]

lemma key (x : ℚ) (h1 : x ≠ -1) (h0 : x ≠ 0) (h1' : x ≠ 1) :
    x.num.natAbs + x.den + 2 ≤ (x - 1/x).num.natAbs + (x - 1/x).den := by
  have hcop : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := x.reduced
    simpa [Int.gcd] using this
  have hxe : x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den x).symm
  have hq1 : (1:ℤ) ≤ (x.den : ℤ) := by exact_mod_cast x.den_pos
  set p := x.num with hp
  set q : ℤ := (x.den : ℤ) with hq
  have hp0 : p ≠ 0 := by
    intro h; apply h0; rw [hxe, h]; simp
  have hqne : q ≠ 0 := by omega
  have hpne : (p:ℚ) ≠ 0 := by exact_mod_cast hp0
  have hqQ : (q:ℚ) ≠ 0 := by exact_mod_cast hqne
  have hsub : x - 1/x = ((p^2 - q^2 : ℤ) : ℚ) / ((p*q : ℤ) : ℚ) := by
    rw [hxe]; push_cast
    field_simp
  have hcop2 : IsCoprime (p^2 - q^2) (p*q) := by
    obtain ⟨u, v, huv⟩ := hcop
    apply IsCoprime.mul_right
    · exact ⟨-v^2, -(u^2*p - v^2*p - 2*u), by linear_combination (v*q - u*p + 1) * huv⟩
    · exact ⟨u^2, -(v^2*q - u^2*q - 2*v), by linear_combination (u*p - v*q + 1) * huv⟩
  have hne : |p| ≠ q := by
    intro h
    have h' : (p.natAbs : ℤ) = (x.den : ℤ) := by rw [Int.abs_eq_natAbs] at h; exact h
    have hn : p.natAbs = x.den := by exact_mod_cast h'
    have hco := x.reduced
    rw [hn] at hco
    have hd1 : x.den = 1 := by simpa using hco
    have hpm : p = 1 ∨ p = -1 := by omega
    have hxp : x = (p:ℚ) := by rw [hxe, hq, hd1]; simp
    rcases hpm with hpm | hpm
    · apply h1'; rw [hxp, hpm]; simp
    · apply h1; rw [hxp, hpm]; simp
  rw [hsub]
  obtain ⟨hn, hd⟩ := nd_lemma (p^2-q^2) (p*q) (mul_ne_zero hp0 hqne) hcop2
  rw [hn]
  have hd' : (((p^2 - q^2 : ℤ) : ℚ) / ((p*q : ℤ) : ℚ)).den = (p*q).natAbs := by
    exact_mod_cast hd
  rw [hd']
  have A := ineq_lemma |p| q (by have := abs_pos.mpr hp0; omega) hq1 hne
  rw [sq_abs] at A
  have B : ((p^2-q^2).natAbs : ℤ) = |p^2 - q^2| := Int.natCast_natAbs _
  have C : ((p*q).natAbs : ℤ) = |p| * q := by
    rw [Int.natAbs_mul, abs_mul]; push_cast; simp [abs_of_pos (show (0:ℤ) < q by omega)]
  have D : (p.natAbs : ℤ) = |p| := (Int.natCast_natAbs _)
  zify
  rw [B, C, D]
  linarith
