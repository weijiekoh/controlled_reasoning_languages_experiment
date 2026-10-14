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
  obtain ⟨ha0, hb0, hc0, hd0⟩ := h₀
  obtain ⟨oa, ob, oc, od⟩ := h₁
  obtain ⟨ab, bc, cd⟩ := h₂
  have hmk : m < k := by
    have : 2^m < 2^k := by
      have h : (b+c)^2 < (a+d)^2 := by nlinarith
      rw [← h₄, ← h₅]
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  have hm2 : 2 ≤ m := by
    by_contra h
    have : m ≤ 1 := by omega
    have : 2^m ≤ 2^1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m-2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, k = n + 2 + s := ⟨k-(n+2), by omega⟩
  have hRpos : 0 < 2^n := by positivity
  have hP : 2^(n+2) = 4*2^n := by ring
  have hPQ : 2^(n+2+s) = 4*2^n*2^s := by rw [pow_add, hP]
  rw [hP] at h₅
  rw [hPQ] at h₄
  generalize hR : 2^n = R at *
  generalize hQ : 2^s = Q at *
  obtain ⟨x, hx⟩ := oa
  obtain ⟨y, hy⟩ := ob
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le (show x ≤ y by omega)
  have hb : b = a + 2*u := by omega
  have hdi : (4*u*(a+u) : ℤ) = 4*R * (b - Q*a) := by
    have hd : (d:ℤ) = 4*R*Q - a := by have := congrArg (Nat.cast (R := ℤ)) h₄; push_cast at this; linarith
    have hc : (c:ℤ) = 4*R - b := by have := congrArg (Nat.cast (R := ℤ)) h₅; push_cast at this; linarith
    have h3 : (a:ℤ)*d = b*c := by exact_mod_cast h₃
    rw [hd, hc] at h3
    have hb' : (b:ℤ) = a + 2*u := by exact_mod_cast hb
    rw [hb'] at h3 ⊢
    linear_combination h3
  have hdn : 4*R ∣ 4*u*(a+u) := by
    have : ((4*R : ℕ):ℤ) ∣ ((4*u*(a+u) : ℕ):ℤ) := by
      push_cast; rw [hdi]; exact Dvd.intro _ rfl
    exact_mod_cast this
  have hvlt : a + u < 2*R := by omega
  have hupos : 0 < u := by omega
  have hu2 : u < R := by omega
  have hodd : Odd u ∨ Odd (a+u) := by
    by_cases h : Odd u
    · exact Or.inl h
    · right
      rw [Nat.not_odd_iff_even] at h
      obtain ⟨z, hz⟩ := h
      exact ⟨x+z, by omega⟩
  have hcopR : ∀ t, Odd t → Nat.Coprime R t := by
    intro t ht
    rw [← hR]
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by intro h; have := Nat.odd_iff.1 ht; omega)
  have hv : a + u = R := by
    rcases hodd with h | h
    · have h1 : R ∣ (a+u) * u := by
        have : 4*R ∣ 4*((a+u)*u) := by rw [show 4*((a+u)*u) = 4*u*(a+u) by ring]; exact hdn
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have h2 := (hcopR u h).dvd_of_dvd_mul_right h1
      obtain ⟨j, hj⟩ := h2
      have : j = 1 := by
        rcases j with _ | _ | j <;> nlinarith
      subst this; omega
    · exfalso
      have h1 : R ∣ u * (a+u) := by
        have : 4*R ∣ 4*(u*(a+u)) := by rw [show 4*(u*(a+u)) = 4*u*(a+u) by ring]; exact hdn
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      have h2 := (hcopR _ h).dvd_of_dvd_mul_right h1
      have := Nat.le_of_dvd hupos h2
      omega
  have hv' : ((a:ℤ)+u) = R := by exact_mod_cast hv
  have hw : (u:ℤ) = b - Q*a := by
    have : (4*R:ℤ)*u = 4*R*(b - Q*a) := by
      rw [hv'] at hdi; linarith
    have hR' : (0:ℤ) < 4*R := by positivity
    exact mul_left_cancel₀ hR'.ne' this
  have hb' : (b:ℤ) = a + 2*u := by exact_mod_cast hb
  have hQa : (Q:ℤ)*a = R := by nlinarith
  have hQa' : Q*a = R := by exact_mod_cast hQa
  have hdv : a ∣ 2^n := ⟨Q, by rw [hR, ← hQa']; ring⟩
  obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdv
  rcases i with _ | i
  · simpa using hai
  · exfalso
    have : Even a := by rw [hai]; exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
    exact (Nat.not_even_iff_odd.2 ⟨x, hx⟩) this
