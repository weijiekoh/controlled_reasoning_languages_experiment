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
: (∀ i j : Finset.range (p ^ 3), h.eval i ≡ h.eval j [ZMOD p ^ 3] → i = j) :=
by
  have hp2 : (2:ℤ) ≤ (p:ℤ) := by exact_mod_cast hp.two_le
  have dm : ∀ z m : ℤ, z % m + m * (z / m) = z := fun z m => Int.emod_add_mul_ediv z m
  have hpz : (0:ℤ) < (p:ℤ) := by linarith
  have hprime : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hm : (0:ℤ) < (p:ℤ)^2 := by positivity
  have taylor : ∀ x y : ℤ, ∃ k : ℤ, h.eval (x+y) = h.eval x + h.derivative.eval x * y + k*y^2 := by
    intro x y
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion h x y
    exact ⟨k, hk⟩
  have red : ∀ z : ℤ, ∃ z' : ℕ, z' < p^2 ∧ z ≡ (z':ℤ) [ZMOD (p:ℤ)^2] ∧ h.eval z ≡ h.eval (z':ℤ) [ZMOD (p:ℤ)^2] := by
    intro z
    have hc : (((z % (p:ℤ)^2).toNat : ℕ) : ℤ) = z % (p:ℤ)^2 := Int.toNat_of_nonneg (Int.emod_nonneg _ hm.ne')
    refine ⟨(z % (p:ℤ)^2).toNat, ?_, ?_, ?_⟩
    · have h1 : z % (p:ℤ)^2 < (p:ℤ)^2 := Int.emod_lt_of_pos _ hm
      have : (((z % (p:ℤ)^2).toNat : ℕ) : ℤ) < ((p^2 : ℕ):ℤ) := by push_cast; rw [hc]; exact h1
      exact_mod_cast this
    · rw [hc]; exact (Int.mod_modEq z _).symm
    · rw [hc]
      obtain ⟨k, hk⟩ := taylor (z % (p:ℤ)^2) ((p:ℤ)^2 * (z / (p:ℤ)^2))
      have hz : z % (p:ℤ)^2 + (p:ℤ)^2 * (z / (p:ℤ)^2) = z := by linarith [dm z ((p:ℤ)^2)]
      rw [hz] at hk
      apply Int.modEq_iff_dvd.mpr
      rw [hk]
      exact ⟨-(h.derivative.eval (z % (p:ℤ)^2) * (z / (p:ℤ)^2) + k * (p:ℤ)^2 * (z/(p:ℤ)^2)^2), by ring⟩
  have factA : ∀ x y : ℤ, h.eval x ≡ h.eval y [ZMOD (p:ℤ)^2] → x ≡ y [ZMOD (p:ℤ)^2] := by
    intro x y hxy
    obtain ⟨x', hx', hxx, hxh⟩ := red x
    obtain ⟨y', hy', hyy, hyh⟩ := red y
    have := hh ⟨x', Finset.mem_range.mpr hx'⟩ ⟨y', Finset.mem_range.mpr hy'⟩ (hxh.symm.trans (hxy.trans hyh))
    have hxy' : x' = y' := congrArg Subtype.val this
    rw [hxy'] at hxx
    exact hxx.trans hyy.symm
  have factB : ∀ a : ℤ, ¬ (p:ℤ) ∣ h.derivative.eval a := by
    intro a hdiv
    obtain ⟨c, hc⟩ := hdiv
    obtain ⟨k, hk⟩ := taylor a p
    have hcong : h.eval (a + p) ≡ h.eval a [ZMOD (p:ℤ)^2] := by
      apply Int.modEq_iff_dvd.mpr
      rw [hk, hc]
      exact ⟨-(c + k), by ring⟩
    have h3 := Int.modEq_iff_dvd.mp (factA _ _ hcong)
    have h4 : (p:ℤ)^2 ∣ (p:ℤ) := by
      have e : a - (a + p) = -p := by ring
      rw [e] at h3
      exact (dvd_neg).mp h3
    have h5 := Int.le_of_dvd hpz h4
    nlinarith
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  have hi' : i < p^3 := Finset.mem_range.mp hi
  have hj' : j < p^3 := Finset.mem_range.mp hj
  change h.eval (i:ℤ) ≡ h.eval (j:ℤ) [ZMOD (p:ℤ)^3] at hij
  have hmod2 : h.eval (i:ℤ) ≡ h.eval (j:ℤ) [ZMOD (p:ℤ)^2] := Int.ModEq.of_dvd ⟨p, by ring⟩ hij
  have hcong := factA _ _ hmod2
  have hiE : (i:ℤ) = (i:ℤ) % (p:ℤ)^2 + (p:ℤ)^2 * ((i:ℤ) / (p:ℤ)^2) := (dm _ _).symm
  have hjE : (j:ℤ) = (i:ℤ) % (p:ℤ)^2 + (p:ℤ)^2 * ((j:ℤ) / (p:ℤ)^2) := by
    have this : (j:ℤ) % (p:ℤ)^2 = (i:ℤ) % (p:ℤ)^2 := hcong.symm
    rw [← this]
    exact (dm _ _).symm
  have hi'' : (i:ℤ) < (p:ℤ)^3 := by exact_mod_cast hi'
  have hj'' : (j:ℤ) < (p:ℤ)^3 := by exact_mod_cast hj'
  have hi0 : (0:ℤ) ≤ i := by positivity
  have hj0 : (0:ℤ) ≤ j := by positivity
  generalize ha : (i:ℤ) % (p:ℤ)^2 = a at hiE hjE
  generalize hs : (i:ℤ) / (p:ℤ)^2 = s at hiE
  generalize ht : (j:ℤ) / (p:ℤ)^2 = t at hjE
  have ha0 : 0 ≤ a := by rw [← ha]; exact Int.emod_nonneg _ hm.ne'
  have ha1 : a < (p:ℤ)^2 := by rw [← ha]; exact Int.emod_lt_of_pos _ hm
  have hs0 : 0 ≤ s := by
    rw [← hs]; exact Int.ediv_nonneg (by positivity) hm.le
  have ht0 : 0 ≤ t := by
    rw [← ht]; exact Int.ediv_nonneg (by positivity) hm.le
  have hs1 : s < p := by
    by_contra hcc; push Not at hcc
    nlinarith [mul_le_mul_of_nonneg_left hcc hm.le]
  have ht1 : t < p := by
    by_contra hcc; push Not at hcc
    nlinarith [mul_le_mul_of_nonneg_left hcc hm.le]
  obtain ⟨k1, hk1⟩ := taylor a ((p:ℤ)^2 * s)
  obtain ⟨k2, hk2⟩ := taylor a ((p:ℤ)^2 * t)
  rw [← hiE] at hk1
  rw [← hjE] at hk2
  have hdvd := Int.modEq_iff_dvd.mp hij
  rw [hk1, hk2] at hdvd
  have h6 : (p:ℤ) ∣ h.derivative.eval a * (t - s) := by
    obtain ⟨c, hc⟩ := hdvd
    have hne : (p:ℤ)^2 ≠ 0 := by positivity
    refine ⟨c - p*(k2*t^2 - k1*s^2), ?_⟩
    apply mul_left_cancel₀ hne
    linear_combination hc
  rcases hprime.dvd_or_dvd h6 with h7 | h7
  · exact absurd h7 (factB a)
  · obtain ⟨c, hc⟩ := h7
    have c1 : c < 1 := by
      by_contra hcc; push Not at hcc
      nlinarith
    have c2 : -1 < c := by
      by_contra hcc; push Not at hcc
      nlinarith
    have hc0 : c = 0 := by omega
    rw [hc0] at hc
    have hts : t = s := by linarith
    have hfin : (i:ℤ) = j := by
      rw [hiE, hjE, hts]
    apply Subtype.ext
    show i = j
    exact_mod_cast hfin
