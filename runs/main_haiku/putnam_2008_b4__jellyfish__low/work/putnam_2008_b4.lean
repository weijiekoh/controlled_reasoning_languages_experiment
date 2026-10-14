import Mathlib

open Filter Topology Set Nat

/--
Let $p$ be a prime number. Let $h(x)$ be a polynomial with integer coefficients such that $h(0), h(1), \dots, h(p^2-1)$ are distinct modulo $p^2$. Show that $h(0), h(1), \dots, h(p^3-1)$ are distinct modulo $p^3$.
-/
theorem putnam_2008_b4
(p : ℕ)
(hp : Nat.Prime p)
(h : Polynomial ℤ)
(hh : ∀ i j : Finset.range (p ^ 2), h.eval i ≡ h.eval j [ZMOD p ^ 2] → i = j)
: (∀ i j : Finset.range (p ^ 3), h.eval i ≡ h.eval j [ZMOD p ^ 3] → i = j) := by
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (2:ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : (0:ℤ) < (p:ℤ)^2 := by positivity
  have red : ∀ x : ℤ, ∃ i : ℕ, i < p^2 ∧ ((p:ℤ)^2 ∣ x - i) := by
    intro x
    have h1 := Int.emod_lt_of_pos x hpos
    have h2 := Int.emod_nonneg x hpos.ne'
    refine ⟨(x % ((p:ℤ)^2)).toNat, ?_, ?_⟩
    · have h3 : ((x % (p:ℤ)^2).toNat : ℤ) < (p:ℤ)^2 := by
        rw [Int.toNat_of_nonneg h2]; exact h1
      exact_mod_cast h3
    · rw [Int.toNat_of_nonneg h2]
      exact ⟨x / (p:ℤ)^2, by rw [Int.emod_def]; ring⟩
  have K : ∀ x y : ℤ, h.eval x ≡ h.eval y [ZMOD (p:ℤ)^2] → x ≡ y [ZMOD (p:ℤ)^2] := by
    intro x y hxy
    obtain ⟨i, hi, hix⟩ := red x
    obtain ⟨j, hj, hjy⟩ := red y
    have e1 : h.eval (i:ℤ) ≡ h.eval x [ZMOD (p:ℤ)^2] := by
      rw [Int.modEq_iff_dvd]; exact dvd_trans hix (Polynomial.sub_dvd_eval_sub x (i:ℤ) h)
    have e2 : h.eval (j:ℤ) ≡ h.eval y [ZMOD (p:ℤ)^2] := by
      rw [Int.modEq_iff_dvd]; exact dvd_trans hjy (Polynomial.sub_dvd_eval_sub y (j:ℤ) h)
    have hij : h.eval (i:ℤ) ≡ h.eval (j:ℤ) [ZMOD (p:ℤ)^2] := e1.trans (hxy.trans e2.symm)
    have := hh ⟨i, Finset.mem_range.mpr hi⟩ ⟨j, Finset.mem_range.mpr hj⟩ hij
    have hij' : i = j := by simpa using this
    have hij'' : (i:ℤ) = (j:ℤ) := by rw [hij']
    rw [Int.modEq_iff_dvd]
    have e : (y - x) = (y - j) - (x - i) := by rw [hij'']; ring
    rw [e]; exact dvd_sub hjy hix
  have BE : ∀ x y : ℤ, ∃ k : ℤ, h.eval (x+y) = h.eval x + h.derivative.eval x * y + k * y^2 := by
    intro x y
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion h x y
    exact ⟨k, hk⟩
  have A : ∀ b : ℤ, ¬ (p:ℤ) ∣ h.derivative.eval b := by
    intro b hb
    obtain ⟨k, hk⟩ := BE b (p:ℤ)
    have hm : h.eval b ≡ h.eval (b + p) [ZMOD (p:ℤ)^2] := by
      rw [Int.modEq_iff_dvd, hk]
      obtain ⟨c, hc⟩ := hb
      rw [hc]
      exact ⟨c + k, by ring⟩
    have h8 := K b (b + p) hm
    rw [Int.modEq_iff_dvd] at h8
    have e : b + (p:ℤ) - b = p := by ring
    rw [e] at h8
    have := Int.le_of_dvd (by linarith) h8
    nlinarith
  have B : ∀ u v : ℤ, h.eval u ≡ h.eval v [ZMOD (p:ℤ)] → u ≡ v [ZMOD (p:ℤ)] := by
    intro u v huv
    have hcop : IsCoprime (h.derivative.eval u) (p:ℤ) :=
      ((Irreducible.coprime_iff_not_dvd hpz.irreducible).mpr (A u)).symm
    obtain ⟨a, b, hab⟩ := hcop
    obtain ⟨m, hm⟩ := (Int.modEq_iff_dvd.mp huv)
    obtain ⟨k, hk⟩ := BE u (p*(m*a))
    have hw : h.eval (u + p*(m*a)) ≡ h.eval v [ZMOD (p:ℤ)^2] := by
      rw [Int.modEq_iff_dvd, hk]
      exact ⟨m*b - k*m^2*a^2, by linear_combination hm - (p*m)*hab⟩
    have h9 := K _ _ hw
    rw [Int.modEq_iff_dvd] at h9
    rw [Int.modEq_iff_dvd]
    have h1 : (p:ℤ) ∣ v - (u + p*(m*a)) := dvd_trans (dvd_pow_self _ two_ne_zero) h9
    have e : v - u = (v - (u + p*(m*a))) + p*(m*a) := by ring
    rw [e]; exact dvd_add h1 (dvd_mul_right _ _)
  intro i j hij
  have ha0 : (0:ℤ) ≤ ((i:ℕ):ℤ) := by positivity
  have hb0 : (0:ℤ) ≤ ((j:ℕ):ℤ) := by positivity
  have ha3 : ((i:ℕ):ℤ) < (p:ℤ)^3 := by
    have := Finset.mem_range.mp i.2; exact_mod_cast this
  have hb3 : ((j:ℕ):ℤ) < (p:ℤ)^3 := by
    have := Finset.mem_range.mp j.2; exact_mod_cast this
  have hab : ((i:ℕ):ℤ) = ((j:ℕ):ℤ) := by
    set a : ℤ := ((i:ℕ):ℤ) with ha
    set b : ℤ := ((j:ℕ):ℤ) with hb
    set D : ℤ := h.derivative.eval a with hD
    have hmod : h.eval a ≡ h.eval b [ZMOD (p:ℤ)] :=
      Int.ModEq.of_dvd (dvd_pow_self (p:ℤ) (by norm_num)) hij
    obtain ⟨t, ht⟩ := (B a b hmod).dvd
    obtain ⟨k, hk⟩ := BE a (b - a)
    rw [show a + (b - a) = b by ring] at hk
    have hdiv : (p:ℤ)^3 ∣ h.eval b - h.eval a := Int.ModEq.dvd hij
    rw [hk, ht] at hdiv
    have e0 : h.eval a + D*(p*t) + k*(p*t)^2 - h.eval a = D*(p*t) + k*(p*t)^2 := by ring
    rw [e0] at hdiv
    have hA : ¬ (p:ℤ) ∣ D := A a
    have h2 : (p:ℤ)^2 ∣ D*(p*t) := by
      have h7 : (p:ℤ)^2 ∣ (p:ℤ)^3 := ⟨p, by ring⟩
      have h3 : (p:ℤ)^2 ∣ D*(p*t) + k*(p*t)^2 := dvd_trans h7 hdiv
      have h6 : (p:ℤ)^2 ∣ k*(p*t)^2 := ⟨k*t^2, by ring⟩
      exact (dvd_add_left h6).mp h3
    obtain ⟨e, he⟩ := h2
    have hDt : D*t = p*e := mul_left_cancel₀ hp0 (by linear_combination he)
    obtain ⟨s, hs⟩ : (p:ℤ) ∣ t := by
      rcases hpz.dvd_or_dvd ⟨e, hDt⟩ with h4 | h4
      · exact absurd h4 hA
      · exact h4
    rw [hs] at hdiv
    obtain ⟨g, hg⟩ := hdiv
    have hDs : D*s = p*(g - k*p*s^2) :=
      mul_left_cancel₀ (pow_ne_zero 2 hp0) (by linear_combination hg)
    rcases hpz.dvd_or_dvd ⟨_, hDs⟩ with h5 | h5
    · exact absurd h5 hA
    · obtain ⟨r, hr⟩ := h5
      have hba : b - a = (p:ℤ)^3 * r := by rw [ht, hs, hr]; ring
      have h10 : b - a = 0 :=
        Int.eq_zero_of_abs_lt_dvd ⟨r, hba⟩ (by rw [abs_lt]; constructor <;> linarith)
      linarith
  exact Subtype.ext (by exact_mod_cast hab)
