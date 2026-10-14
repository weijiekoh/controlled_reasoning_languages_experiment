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
  have hp2 : 2 ≤ p := hp.two_le
  have hpZ2 : (2:ℤ) ≤ p := by exact_mod_cast hp2
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpZ : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have taylor : ∀ x y : ℤ, ∃ k : ℤ, h.eval (x+y) = h.eval x + (Polynomial.derivative h).eval x * y + k*y^2 := by
    intro x y
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion h x y
    exact ⟨k, hk⟩
  have hA : ∀ n : ℕ, ¬ (p:ℤ) ∣ (Polynomial.derivative h).eval (n:ℤ) := by
    intro n hdn
    obtain ⟨m, hm⟩ : ∃ m, m = n % p := ⟨_, rfl⟩
    have hnm : (n:ℤ) = (m:ℤ) + (p:ℤ) * ((n/p : ℕ):ℤ) := by
      have := Nat.mod_add_div n p
      rw [← hm] at this
      exact_mod_cast this.symm
    have hpm : (p:ℤ) ∣ (n:ℤ) - (m:ℤ) := ⟨((n/p:ℕ):ℤ), by linarith⟩
    have hdm : (p:ℤ) ∣ (Polynomial.derivative h).eval (m:ℤ) := by
      have h1 : (p:ℤ) ∣ (Polynomial.derivative h).eval (n:ℤ) - (Polynomial.derivative h).eval (m:ℤ) :=
        dvd_trans hpm (Polynomial.sub_dvd_eval_sub _ _ _)
      have := dvd_sub hdn h1
      rwa [sub_sub_cancel] at this
    have hmlt : m < p := by rw [hm]; exact Nat.mod_lt _ (by omega)
    have hmp : m + p < p^2 := by nlinarith
    obtain ⟨k, hk⟩ := taylor (m:ℤ) (p:ℤ)
    obtain ⟨c, hc⟩ := hdm
    have hcong : h.eval ((m:ℕ):ℤ) ≡ h.eval (((m+p : ℕ)):ℤ) [ZMOD (p:ℤ)^2] := by
      rw [Int.modEq_iff_dvd]
      have e : (((m+p:ℕ)):ℤ) = (m:ℤ) + (p:ℤ) := by push_cast; ring
      rw [e, hk]
      exact ⟨c + k, by linear_combination (p:ℤ) * hc⟩
    have := hh ⟨m, Finset.mem_range.mpr (by nlinarith)⟩ ⟨m+p, Finset.mem_range.mpr hmp⟩ hcong
    have h2 : m = m + p := congrArg (fun x : Finset.range (p^2) => (x:ℕ)) this
    omega
  have expand : ∀ r s : ℕ, ∃ k : ℤ, h.eval (((r + p^2*s : ℕ)):ℤ) = h.eval (r:ℤ) + (Polynomial.derivative h).eval (r:ℤ) * ((p:ℤ)^2*(s:ℤ)) + k*((p:ℤ)^2*(s:ℤ))^2 := by
    intro r s
    obtain ⟨k, hk⟩ := taylor (r:ℤ) ((p:ℤ)^2*(s:ℤ))
    have e : (((r + p^2*s : ℕ)):ℤ) = (r:ℤ) + (p:ℤ)^2*(s:ℤ) := by push_cast; ring
    exact ⟨k, by rw [e, hk]⟩
  intro i j hij
  obtain ⟨a, ha⟩ := i
  obtain ⟨b, hb⟩ := j
  rw [Finset.mem_range] at ha hb
  have hij' : h.eval ((a:ℕ):ℤ) ≡ h.eval ((b:ℕ):ℤ) [ZMOD (p:ℤ)^3] := by
    exact hij
  apply Subtype.ext
  obtain ⟨ra, sa, hra, rfl, hsa⟩ : ∃ r s : ℕ, r < p^2 ∧ a = r + p^2*s ∧ s < p :=
    ⟨a % p^2, a / p^2, Nat.mod_lt _ (by positivity), (Nat.mod_add_div a _).symm, by
      have h3 : p^3 = p*p^2 := by ring
      rw [h3] at ha
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr ha⟩
  obtain ⟨rb, tb, hrb, rfl, htb⟩ : ∃ r s : ℕ, r < p^2 ∧ b = r + p^2*s ∧ s < p :=
    ⟨b % p^2, b / p^2, Nat.mod_lt _ (by positivity), (Nat.mod_add_div b _).symm, by
      have h3 : p^3 = p*p^2 := by ring
      rw [h3] at hb
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr hb⟩
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hij'
  obtain ⟨k1, eA⟩ := expand ra sa
  obtain ⟨k2, eB⟩ := expand rb tb
  have hdiv : (p:ℤ)^2 ∣ h.eval (rb:ℤ) - h.eval (ra:ℤ) :=
    ⟨(p:ℤ)*c - (Polynomial.derivative h).eval (rb:ℤ) * tb - k2 * (p:ℤ)^2 * (tb:ℤ)^2
      + (Polynomial.derivative h).eval (ra:ℤ) * sa + k1 * (p:ℤ)^2 * (sa:ℤ)^2,
     by linear_combination hc + eA - eB⟩
  have hrr : ra = rb := by
    have := hh ⟨ra, Finset.mem_range.mpr hra⟩ ⟨rb, Finset.mem_range.mpr hrb⟩ (Int.modEq_iff_dvd.mpr hdiv)
    exact congrArg (fun x : Finset.range (p^2) => (x:ℕ)) this
  subst rb
  have key : (p:ℤ)^2 * ((Polynomial.derivative h).eval (ra:ℤ) * ((tb:ℤ) - sa))
      = (p:ℤ)^2 * ((p:ℤ) * (c - p*(k2*(tb:ℤ)^2 - k1*(sa:ℤ)^2))) := by
    linear_combination hc - eB + eA
  have hdiv2 : (p:ℤ) ∣ (Polynomial.derivative h).eval (ra:ℤ) * ((tb:ℤ) - sa) :=
    ⟨_, mul_left_cancel₀ (pow_ne_zero 2 hp0) key⟩
  rcases hpZ.dvd_or_dvd hdiv2 with h1 | ⟨m, hm⟩
  · exact absurd h1 (hA ra)
  · have hs1 : (sa:ℤ) < p := by exact_mod_cast hsa
    have hs2 : (tb:ℤ) < p := by exact_mod_cast htb
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h0 | h0 | h0 <;> nlinarith
    have hts : (tb:ℤ) = sa := by rw [hm0] at hm; linarith
    have hts' : tb = sa := by exact_mod_cast hts
    subst hts'
    rfl
