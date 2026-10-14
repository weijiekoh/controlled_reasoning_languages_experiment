import Mathlib

noncomputable abbrev putnam_2024_a4_solution : Set ℕ := {7}

lemma a4_intcase (P A c1 c2 c3 : ℤ) (hP : 11 ≤ P) (hA1 : -3 ≤ A) (hA2 : A ≤ 0)
    (h1 : A ≤ c1) (h1' : c1 ≤ A + 3) (h2 : A ≤ c2) (h2' : c2 ≤ A + 3)
    (h3 : A ≤ c3) (h3' : c3 ≤ A + 3)
    (n1 : c1 ≠ 0) (n2 : c2 ≠ 0) (n3 : c3 ≠ 0) (n13 : c1 ≠ c3)
    (hd : P ∣ c2 ^ 2 - c1 * c3) : False := by
  have hkey : ∀ v : ℤ, P ∣ v → -7 ≤ v → v ≤ 7 → v = 0 := by
    intro v hv l u
    apply Int.eq_zero_of_abs_lt_dvd hv
    rw [abs_lt]
    constructor <;> omega
  have b1l : -3 ≤ c1 := by omega
  have b1u : c1 ≤ 3 := by omega
  have b2l : -3 ≤ c2 := by omega
  have b2u : c2 ≤ 3 := by omega
  have b3l : -3 ≤ c3 := by omega
  have b3u : c3 ≤ 3 := by omega
  interval_cases A <;> interval_cases c1 <;> interval_cases c2 <;> interval_cases c3 <;>
    first
    | omega
    | (have h7 := hkey _ hd (by norm_num) (by norm_num); norm_num at h7)

lemma a4_core (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (a r : ℤ) (hr1 : 1 ≤ r)
    (hr2 : r ≤ (p : ℤ) - 1)
    (e : ℕ → ℕ) (hbij : Set.BijOn e (Set.Icc 0 (p - 5 : ℕ)) (Set.Icc 0 (p - 5 : ℕ)))
    (hdiv : ∀ n, 1 ≤ n ∧ n ≤ (p - 5 : ℕ) →
      (p : ℤ) ∣ a ^ (e n : ℕ) - a ^ (e (n - 1) : ℕ) - r) : False := by
  haveI := Fact.mk hp
  obtain ⟨m, hm⟩ : ∃ m, m = p - 5 := ⟨_, rfl⟩
  rw [← hm] at hbij hdiv
  have hm6 : 6 ≤ m := by omega
  have hR0 : (r : ZMod p) ≠ 0 := by
    intro h
    have h' : (p : ℤ) ∣ r := (ZMod.intCast_zmod_eq_zero_iff_dvd r p).mp h
    have := Int.le_of_dvd (by omega) h'
    omega
  have hcast : ∀ n, 1 ≤ n → n ≤ m →
      (a : ZMod p) ^ (e n) - (a : ZMod p) ^ (e (n - 1)) = (r : ZMod p) := by
    intro n h1 h2
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hdiv n ⟨h1, h2⟩)
    push_cast at h
    linear_combination h
  set x : ZMod p := (a : ZMod p) with hx
  set R : ZMod p := (r : ZMod p) with hRdef
  have hA : ∀ n, n ≤ m → x ^ (e n) = x ^ (e 0) + (n : ZMod p) * R := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := hcast (k + 1) (by omega) hk
      simp only [Nat.add_sub_cancel] at h1
      have h2 := ih (by omega)
      push_cast
      linear_combination h1 + h2
  have hmaps : ∀ n, n ≤ m → e n ≤ m := fun n hn =>
    (hbij.mapsTo (show n ∈ Set.Icc 0 m from ⟨Nat.zero_le _, hn⟩)).2
  have hsurj : ∀ i, i ≤ m → ∃ n, n ≤ m ∧ e n = i := by
    intro i hi
    obtain ⟨n, hn, hni⟩ := hbij.surjOn (show i ∈ Set.Icc 0 m from ⟨Nat.zero_le _, hi⟩)
    exact ⟨n, hn.2, hni⟩
  have hB : ∀ i j, i ≤ m → j ≤ m → x ^ i = x ^ j → i = j := by
    intro i j hi hj hij
    obtain ⟨n, hn, rfl⟩ := hsurj i hi
    obtain ⟨n', hn', rfl⟩ := hsurj j hj
    have h1 := hA n hn
    have h2 := hA n' hn'
    have h3 : (n : ZMod p) * R = (n' : ZMod p) * R := by
      linear_combination -h1 + h2 + hij
    have h4 : (n : ZMod p) = (n' : ZMod p) := mul_right_cancel₀ hR0 h3
    have h5 : n = n' := by
      have h6 := (ZMod.natCast_eq_natCast_iff' n n' p).mp h4
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h6
    rw [h5]
  have hx0 : x ≠ 0 := by
    intro h
    have := hB 1 2 (by omega) (by omega) (by rw [h]; simp)
    omega
  have hfer : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hdvd : orderOf x ∣ p - 1 := orderOf_dvd_of_pow_eq_one hfer
  have hdpos : 0 < orderOf x :=
    Nat.pos_of_ne_zero (fun h => by rw [h, zero_dvd_iff] at hdvd; omega)
  have hdge : m + 1 ≤ orderOf x := by
    by_contra hlt
    push_neg at hlt
    have h1 : x ^ orderOf x = x ^ 0 := by rw [pow_orderOf_eq_one, pow_zero]
    have := hB (orderOf x) 0 (by omega) (by omega) h1
    omega
  have hp1 : p - 1 = m + 4 := by omega
  have hd : orderOf x = p - 1 := by
    obtain ⟨q, hq⟩ := hdvd
    rcases Nat.lt_or_ge q 2 with hq2 | hq2
    · interval_cases q
      · simp at hq <;> omega
      · simp at hq <;> omega
    · exfalso
      have h1 : orderOf x * 2 ≤ orderOf x * q := Nat.mul_le_mul_left _ hq2
      nlinarith
  have hL1 : ∀ i j, i < j → j < p - 1 → x ^ i = x ^ j → False := by
    intro i j hij' hj hxij
    have h1 : x ^ (j - i) = 1 := by
      have : x ^ i * x ^ (j - i) = x ^ i * 1 := by
        rw [mul_one, ← pow_add, show i + (j - i) = j by omega]
        exact hxij.symm
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) this
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hd] at h3
    have h2 := Nat.le_of_dvd (by omega) h3
    omega
  have hL : ∀ i j, i < p - 1 → j < p - 1 → x ^ i = x ^ j → i = j := by
    intro i j hi hj hij
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact (hL1 i j h hj hij).elim
    · exact h
    · exact (hL1 j i h hi hij.symm).elim
  have hrep : ∀ t : ZMod p, ∃ k : ℕ, k < p ∧ t = x ^ (e 0) + (k : ZMod p) * R := by
    intro t
    refine ⟨((t - x ^ (e 0)) / R).val, ZMod.val_lt _, ?_⟩
    rw [ZMod.natCast_zmod_val, div_mul_cancel₀ _ hR0]
    ring
  obtain ⟨k0, hk0p, hk0⟩ := hrep 0
  have hk0m : m + 1 ≤ k0 := by
    by_contra hlt
    push_neg at hlt
    have h1 := hA k0 (by omega)
    have h2 : x ^ (e k0) = 0 := by rw [h1]; exact hk0.symm
    exact pow_ne_zero _ hx0 h2
  have hy : ∀ j, 1 ≤ j → j ≤ 3 →
      ∃ k : ℕ, m + 1 ≤ k ∧ k < p ∧ x ^ (m + j) = x ^ (e 0) + (k : ZMod p) * R := by
    intro j h1 h2
    obtain ⟨k, hkp, hk⟩ := hrep (x ^ (m + j))
    refine ⟨k, ?_, hkp, hk⟩
    by_contra hlt
    push_neg at hlt
    have h3 := hA k (by omega)
    have h4 : x ^ (e k) = x ^ (m + j) := by rw [h3, hk]
    have h5 := hL (e k) (m + j) (by have := hmaps k (by omega); omega) (by omega) h4
    have := hmaps k (by omega)
    omega
  obtain ⟨k1, hk1m, hk1p, hk1⟩ := hy 1 le_rfl (by norm_num)
  obtain ⟨k2, hk2m, hk2p, hk2⟩ := hy 2 (by norm_num) (by norm_num)
  obtain ⟨k3, hk3m, hk3p, hk3⟩ := hy 3 (by norm_num) le_rfl
  have hc1 : x ^ (m + 1) = (((k1 : ℤ) - k0 : ℤ) : ZMod p) * R := by
    push_cast; linear_combination hk1 - hk0
  have hc2 : x ^ (m + 2) = (((k2 : ℤ) - k0 : ℤ) : ZMod p) * R := by
    push_cast; linear_combination hk2 - hk0
  have hc3 : x ^ (m + 3) = (((k3 : ℤ) - k0 : ℤ) : ZMod p) * R := by
    push_cast; linear_combination hk3 - hk0
  have hrel : x ^ (m + 2) * x ^ (m + 2) = x ^ (m + 1) * x ^ (m + 3) := by ring
  rw [hc1, hc2, hc3] at hrel
  push_cast at hrel
  have hQ : R ^ 2 * (((k2 : ZMod p) - k0) ^ 2 - ((k1 : ZMod p) - k0) * ((k3 : ZMod p) - k0))
      = 0 := by
    linear_combination hrel
  have hQ' : ((k2 : ZMod p) - k0) ^ 2 - ((k1 : ZMod p) - k0) * ((k3 : ZMod p) - k0) = 0 :=
    (mul_eq_zero.mp hQ).resolve_left (pow_ne_zero 2 hR0)
  have hdivZ : (p : ℤ) ∣ ((k2 : ℤ) - k0) ^ 2 - ((k1 : ℤ) - k0) * ((k3 : ℤ) - k0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hQ'
  have n1 : (k1 : ℤ) - k0 ≠ 0 := by
    intro h
    have hk : k1 = k0 := by omega
    apply pow_ne_zero (m + 1) hx0
    rw [hk1, hk]
    exact hk0.symm
  have n2 : (k2 : ℤ) - k0 ≠ 0 := by
    intro h
    have hk : k2 = k0 := by omega
    apply pow_ne_zero (m + 2) hx0
    rw [hk2, hk]
    exact hk0.symm
  have n3 : (k3 : ℤ) - k0 ≠ 0 := by
    intro h
    have hk : k3 = k0 := by omega
    apply pow_ne_zero (m + 3) hx0
    rw [hk3, hk]
    exact hk0.symm
  have n13 : (k1 : ℤ) - k0 ≠ (k3 : ℤ) - k0 := by
    intro h
    have hk : k1 = k3 := by omega
    have h' : x ^ (m + 1) = x ^ (m + 3) := by rw [hk1, hk3, hk]
    have := hL (m + 1) (m + 3) (by omega) (by omega) h'
    omega
  exact a4_intcase (p : ℤ) ((p : ℤ) - 4 - k0) ((k1 : ℤ) - k0) ((k2 : ℤ) - k0) ((k3 : ℤ) - k0)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) n1 n2 n3 n13 hdivZ
/--
Find all primes $p > 5$ for which there exists an integer $a$ and an integer $r$ satisfying $1 \le r \le p - 1$ with the following property:
the sequence $1, a, a^2, ..., a^{p-5}$ can be rearranged to form a sequence $b_0, ..., b_{p-5}$ such that $b_n - b_{n-1} - r$ is divisible by $p$ for $1 \le n \le p - 5$.
-/
theorem putnam_2024_a4 :
    {p : ℕ | p.Prime ∧ 5 < p ∧ ∃ a r : ℤ, 1 ≤ r ∧ r ≤ p - 1 ∧
      ∃ e : ℕ → ℕ, Set.BijOn e (Set.Icc 0 (p - 5 : ℕ)) (Set.Icc 0 (p - 5 : ℕ)) ∧
        ∀ n, 1 ≤ n ∧ n ≤ (p - 5 : ℕ) →
          (p : ℤ) ∣ a ^ (e n : ℕ) - a ^ (e (n - 1) : ℕ) - r} =
    putnam_2024_a4_solution := by
  ext p
  simp only [Set.mem_setOf_eq, putnam_2024_a4_solution, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, h5, a, r, hr1, hr2, e, hbij, hdiv⟩
    by_contra hne
    have h11 : 11 ≤ p := by
      by_contra h
      interval_cases p <;> first | exact absurd rfl hne | (norm_num at hp)
    exact a4_core p hp h11 a r hr1 hr2 e hbij hdiv
  · rintro rfl
    refine ⟨by norm_num, by norm_num, 3, 1, by norm_num, by norm_num,
      fun n => if n = 1 then 2 else if n = 2 then 1 else n, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro n hn
        simp only [Set.mem_Icc] at hn ⊢
        split_ifs <;> omega
      · intro n hn n' hn' h
        simp only [Set.mem_Icc] at hn hn'
        dsimp only at h
        split_ifs at h <;> omega
      · intro t ht
        simp only [Set.mem_Icc] at ht
        have ht2 : t ≤ 2 := by omega
        interval_cases t
        · exact ⟨0, by norm_num, by norm_num⟩
        · exact ⟨2, by norm_num, by norm_num⟩
        · exact ⟨1, by norm_num, by norm_num⟩
    · intro n hn
      obtain ⟨h1, h2⟩ := hn
      have h3 : n ≤ 2 := by omega
      interval_cases n <;> norm_num
