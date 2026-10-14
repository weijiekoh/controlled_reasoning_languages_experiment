import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem imo_1984_p6
  (a b c d k m : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h₂ : a < b ∧ b < c ∧ c < d)
  (h₃ : a * d = b * c)
  (h₄ : a + d = 2^k)
  (h₅ : b + c = 2^m) :
  a = 1 := by
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  obtain ⟨oa, ob, oc, od⟩ := h₁
  obtain ⟨ab, bc, cd⟩ := h₂
  have hkm : m < k := by
    have : b + c < a + d := by
      by_contra hh
      push_neg at hh
      have : (a+d)^2 ≤ (b+c)^2 := Nat.pow_le_pow_left hh 2
      nlinarith
    rw [h₄, h₅] at this
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  obtain ⟨e, rfl⟩ : ∃ e, k = m + e := ⟨k - m, by omega⟩
  have hpow : (2:ℤ)^(m+e) = 2^m * 2^e := pow_add _ _ _
  have hdz : (d:ℤ) = 2^(m+e) - a := by
    have : ((a + d : ℕ):ℤ) = ((2^(m+e) : ℕ):ℤ) := by rw [h₄]
    push_cast at this; linarith
  have hcz : (c:ℤ) = 2^m - b := by
    have : ((b + c : ℕ):ℤ) = ((2^m : ℕ):ℤ) := by rw [h₅]
    push_cast at this; linarith
  have h3z : (a:ℤ) * d = b * c := by exact_mod_cast h₃
  rw [hdz, hcz] at h3z
  have H : (2:ℤ)^m * (b - 2^e * a) = ((b:ℤ) - a) * (b + a) := by
    rw [hpow] at h3z; linarith
  obtain ⟨p, hp⟩ := oa
  obtain ⟨q, hq⟩ := ob
  have hpq : p < q := by omega
  obtain ⟨u, hu⟩ : ∃ u, u = q - p := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = q + p + 1 := ⟨_, rfl⟩
  have hbu : b - a = 2 * u := by omega
  have hbv : a + b = 2 * v := by omega
  have huv : u + v = b := by omega
  have hupos : 0 < u := by omega
  have hm2 : 2 ≤ m := by
    by_contra hh
    have : m ≤ 1 := by omega
    have : 2^m ≤ 2^1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hb2 : b < 2^(n+1) := by
    have : 2^(n+2) = 2 * 2^(n+1) := by ring
    omega
  have hdiv : 2^n ∣ u * v := by
    have h1 : ((2:ℤ)^(n+2)) ∣ ((2 * u : ℕ):ℤ) * ((2 * v : ℕ):ℤ) := by
      have e1 : ((2 * u : ℕ):ℤ) = (b:ℤ) - a := by push_cast; omega
      have e2 : ((2 * v : ℕ):ℤ) = (b:ℤ) + a := by push_cast; omega
      rw [e1, e2, ← H]
      exact Dvd.intro _ rfl
    have h2 : ((2^n * 4 : ℕ):ℤ) ∣ ((4 * (u * v) : ℕ):ℤ) := by
      push_cast at h1 ⊢
      have : (2:ℤ)^(n+2) = 2^n*4 := by ring
      rw [this] at h1
      convert h1 using 1; ring
    have h3 := Int.natCast_dvd_natCast.1 h2
    have : 4 * 2^n ∣ 4 * (u*v) := by rw [mul_comm 4]; exact h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have hcopo : ∀ x : ℕ, Odd x → ∀ j : ℕ, Nat.Coprime (2^j) x := by
    intro x hx j
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rcases hx with ⟨r, hr⟩; omega
  have hvv : v = 2^n := by
    have hvb : v < b := by omega
    rcases Nat.even_or_odd u with he | ho
    · have hvo : Odd v := by
        rcases Nat.even_or_odd v with hve | hvo
        · exfalso
          have : Even b := by rw [← huv]; exact he.add hve
          rw [Nat.even_iff] at this; omega
        · exact hvo
      have hc2 : Nat.Coprime (2^n) v := hcopo _ hvo _
      have : 2^n ∣ u := hc2.dvd_of_dvd_mul_right hdiv
      obtain ⟨t, ht⟩ := this
      exfalso
      have : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have : 2^n ≤ u := by rw [ht]; exact Nat.le_mul_of_pos_right _ this
      have : 2^(n+1) = 2^n*2 := by ring
      omega
    · have hc2 : Nat.Coprime (2^n) u := hcopo _ ho _
      have : 2^n ∣ v := hc2.dvd_of_dvd_mul_left hdiv
      obtain ⟨t, ht⟩ := this
      have : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have : t < 2 := by
        by_contra hh
        have : 2^n * 2 ≤ 2^n * t := Nat.mul_le_mul_left _ (by omega)
        have : 2^(n+1) = 2^n*2 := by ring
        omega
      have : t = 1 := by omega
      subst this; omega
  have hab : a + b = 2^(n+1) := by rw [hbv, hvv]; ring
  have habz : (a:ℤ) + b = 2^(n+1) := by exact_mod_cast hab
  have hbaz : (b:ℤ) - a = 2^(n+1) - 2*a := by linarith
  have H2 : (2:ℤ)^(n+2) * (b - 2^e * a) = (2^(n+1) - 2*a) * 2^(n+1) := by
    have h5 := H
    rw [hbaz, show (b:ℤ) + a = 2^(n+1) by linarith] at h5
    exact h5
  have H3 : (a:ℤ) * 2^(e+1) = 2^(n+1) := by
    have hp2 : (0:ℤ) < 2^(n+1) := by positivity
    have : (2:ℤ)^(n+2) = 2 * 2^(n+1) := by ring
    rw [this] at H2
    have h4 : 2 * ((b:ℤ) - 2^e * a) = 2^(n+1) - 2*a := by
      apply mul_right_cancel₀ hp2.ne'; linarith
    have : (2:ℤ)^(e+1) = 2 * 2^e := by ring
    rw [this]; linarith
  have H4 : a * 2^(e+1) = 2^(n+1) := by exact_mod_cast H3
  have hdv : a ∣ 2^(n+1) := ⟨_, H4.symm⟩
  have hcop : Nat.Coprime a (2^(n+1)) := (hcopo a ⟨p, hp⟩ (n+1)).symm
  exact Nat.Coprime.eq_one_of_dvd hcop hdv
