import Mathlib

noncomputable abbrev putnam_2024_a4_solution : Set ℕ := {7}
/--
Find all primes $p > 5$ for which there exists an integer $a$ and an integer $r$ satisfying $1 \le r \le p - 1$ with the following property:
the sequence $1, a, a^2, ..., a^{p-5}$ can be rearranged to form a sequence $b_0, ..., b_{p-5}$ such that $b_n - b_{n-1} - r$ is divisible by $p$ for $1 \le n \le p - 5$.
-/
theorem putnam_2024_a4 :
    {p : ℕ | p.Prime ∧ 5 < p ∧ ∃ a r : ℤ, 1 ≤ r ∧ r ≤ p - 1 ∧
      ∃ e : ℕ → ℕ, Set.BijOn e (Set.Icc 0 (p - 5 : ℕ)) (Set.Icc 0 (p - 5 : ℕ)) ∧
        ∀ n, 1 ≤ n ∧ n ≤ (p - 5 : ℕ) →
          (p : ℤ) ∣ a ^ (e n : ℕ) - a ^ (e (n - 1) : ℕ) - r} =
    putnam_2024_a4_solution :=
  by
  ext p
  simp only [Set.mem_setOf_eq, putnam_2024_a4_solution, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, h5, a, r, hr1, hr2, e, hbij, hrec⟩
    by_contra hne
    have h11 : 11 ≤ p := by
      by_contra h
      have hp10 : p < 11 := by omega
      interval_cases p <;> first | exact hne rfl | exact absurd hp (by norm_num)
    haveI := Fact.mk hp
    haveI : NeZero p := ⟨by omega⟩
    have hrec' : ∀ n, 1 ≤ n → n ≤ p - 5 →
        (a : ZMod p) ^ (e n) = (a : ZMod p) ^ (e (n - 1)) + (r : ZMod p) := by
      intro n h1 h2
      have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 (hrec n ⟨h1, h2⟩)
      push_cast at h
      linear_combination h
    have hR : (r : ZMod p) ≠ 0 := by
      intro h
      have h' := Int.le_of_dvd (by omega) ((ZMod.intCast_zmod_eq_zero_iff_dvd r p).1 h)
      omega
    have hlin : ∀ n, n ≤ p - 5 →
        (a : ZMod p) ^ (e n) = (a : ZMod p) ^ (e 0) + (n : ZMod p) * (r : ZMod p) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        rw [hrec' (k + 1) (by omega) hk, Nat.add_sub_cancel, ih (by omega)]
        push_cast
        ring
    have hinjN : ∀ m n : ℕ, m ≤ p - 5 → n ≤ p - 5 → (m : ZMod p) = (n : ZMod p) → m = n := by
      intro m n hm hn h
      have h2 : (((m : ℤ) - (n : ℤ) : ℤ) : ZMod p) = 0 := by
        push_cast
        rw [h, sub_self]
      have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h2
      have h4 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
      omega
    have hsurj : ∀ j, j ≤ p - 5 → ∃ n, n ≤ p - 5 ∧ e n = j := by
      intro j hj
      obtain ⟨n, hn, hen⟩ := hbij.surjOn (show j ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, hj⟩)
      exact ⟨n, hn.2, hen⟩
    have hD : ∀ i j, i ≤ p - 5 → j ≤ p - 5 → (a : ZMod p) ^ i = (a : ZMod p) ^ j → i = j := by
      intro i j hi hj hij
      obtain ⟨ni, hni, heni⟩ := hsurj i hi
      obtain ⟨nj, hnj, hnj'⟩ := hsurj j hj
      have h1 := hlin ni hni
      have h2 := hlin nj hnj
      rw [heni] at h1
      rw [hnj'] at h2
      have this := h1.symm.trans (hij.trans h2)
      have h3 : (ni : ZMod p) * (r : ZMod p) = (nj : ZMod p) * (r : ZMod p) := by
        linear_combination this
      have h4 := hinjN ni nj hni hnj (mul_right_cancel₀ hR h3)
      rw [← heni, ← hnj', h4]
    have ha0 : (a : ZMod p) ≠ 0 := by
      intro h
      have h1 : (a : ZMod p) ^ 1 = (a : ZMod p) ^ 2 := by simp [h]
      have := hD 1 2 (by omega) (by omega) h1
      omega
    have hfermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
    have hdpos : orderOf (a : ZMod p) ≠ 0 := by
      intro h0
      have h1 := orderOf_dvd_of_pow_eq_one hfermat
      rw [h0] at h1
      have h2 := Nat.eq_zero_of_zero_dvd h1
      omega
    have hdN : p - 5 < orderOf (a : ZMod p) := by
      by_contra hcon
      push_neg at hcon
      have := hD _ 0 hcon (by omega) (by rw [pow_orderOf_eq_one, pow_zero])
      exact hdpos this
    have hdivl : ∀ d k : ℕ, p - 1 = d * k → p - 5 < d → d = p - 1 := by
      intro d k hk hd
      rcases k with _ | _ | k
      · simp at hk; omega
      · simp at hk; omega
      · exfalso
        have h2 : d * 2 ≤ d * (k + 1 + 1) := Nat.mul_le_mul_left d (by omega)
        rw [← hk] at h2
        omega
    obtain ⟨k', hk'⟩ := orderOf_dvd_of_pow_eq_one hfermat
    have hdeq : orderOf (a : ZMod p) = p - 1 := hdivl _ _ hk' hdN
    have hD2 : ∀ i j : ℕ, i < p - 1 → j < p - 1 →
        (a : ZMod p) ^ i = (a : ZMod p) ^ j → i = j := by
      have key1 : ∀ i j : ℕ, i < p - 1 → j < p - 1 → i ≤ j →
          (a : ZMod p) ^ i = (a : ZMod p) ^ j → i = j := by
        intro i j hi hj hij h
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
        have h1 : (a : ZMod p) ^ (i + d) = (a : ZMod p) ^ i * (a : ZMod p) ^ d :=
          pow_add _ _ _
        have h2 : (a : ZMod p) ^ d = 1 := by
          have h5 : (a : ZMod p) ^ i * (a : ZMod p) ^ d = (a : ZMod p) ^ i * 1 := by
            rw [mul_one, ← h1, h]
          exact mul_left_cancel₀ (pow_ne_zero _ ha0) h5
        have h3 := orderOf_dvd_of_pow_eq_one h2
        rw [hdeq] at h3
        by_contra hne'
        have := Nat.le_of_dvd (by omega) h3
        omega
      intro i j hi hj h
      rcases le_total i j with hij | hij
      · exact key1 i j hi hj hij h
      · exact (key1 j i hj hi hij h.symm).symm
    have hnotA : ∀ m : ℕ, p - 4 ≤ m → m < p - 1 → ∀ n, n ≤ p - 5 →
        (a : ZMod p) ^ m ≠ (a : ZMod p) ^ (e n) := by
      intro m hm1 hm2 n hn h
      have hen : e n ≤ p - 5 :=
        (hbij.mapsTo (show n ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, hn⟩)).2
      have h1 := hD2 m (e n) (by omega) (by omega) h
      omega
    have hcomp : ∀ z : ZMod p, (∀ n, n ≤ p - 5 → z ≠ (a : ZMod p) ^ (e n)) →
        ∃ k : ℤ, -4 ≤ k ∧ k ≤ -1 ∧ z = (a : ZMod p) ^ (e 0) + (k : ZMod p) * (r : ZMod p) := by
      intro z hz
      obtain ⟨t, ht⟩ : ∃ t : ZMod p, t = (z - (a : ZMod p) ^ (e 0)) * (r : ZMod p)⁻¹ :=
        ⟨_, rfl⟩
      have hzt : z = (a : ZMod p) ^ (e 0) + ((t.val : ℕ) : ZMod p) * (r : ZMod p) := by
        rw [ZMod.natCast_zmod_val, ht, mul_assoc, inv_mul_cancel₀ hR, mul_one]
        ring
      have hlt := ZMod.val_lt t
      by_cases hn : t.val ≤ p - 5
      · exact absurd (hzt.trans (hlin _ hn).symm) (hz _ hn)
      · refine ⟨(t.val : ℤ) - p, by omega, by omega, ?_⟩
        simp only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, sub_zero]
        exact hzt
    have key : ∀ u v w s : ℤ, -4 ≤ u → u ≤ -1 → -4 ≤ v → v ≤ -1 → -4 ≤ w → w ≤ -1 →
        -4 ≤ s → s ≤ -1 → u ≠ v → u ≠ w → u ≠ s → v ≠ w → v ≠ s → w ≠ s →
        (-7 ≤ (w - u) ^ 2 - (v - u) * (s - u) ∧ (w - u) ^ 2 - (v - u) * (s - u) ≤ 7 ∧
          (w - u) ^ 2 - (v - u) * (s - u) ≠ 0) := by
      intro u v w s hu1 hu2 hv1 hv2 hw1 hw2 hs1 hs2 h1 h2 h3 h4 h5 h6
      interval_cases u <;> interval_cases v <;> interval_cases w <;> interval_cases s <;>
        first | omega | norm_num
    obtain ⟨k0, hk0a, hk0b, hk0⟩ := hcomp 0 (fun n _ h => pow_ne_zero _ ha0 h.symm)
    obtain ⟨k1, hk1a, hk1b, hk1⟩ :=
      hcomp ((a : ZMod p) ^ (p - 2)) (fun n hn => hnotA (p - 2) (by omega) (by omega) n hn)
    obtain ⟨k2, hk2a, hk2b, hk2⟩ :=
      hcomp ((a : ZMod p) ^ (p - 3)) (fun n hn => hnotA (p - 3) (by omega) (by omega) n hn)
    obtain ⟨k3, hk3a, hk3b, hk3⟩ :=
      hcomp ((a : ZMod p) ^ (p - 4)) (fun n hn => hnotA (p - 4) (by omega) (by omega) n hn)
    have hx2 : ((a : ZMod p) ^ (p - 2)) ^ 2 = (a : ZMod p) ^ (p - 3) := by
      rw [← pow_mul, show (p - 2) * 2 = (p - 1) + (p - 3) by omega, pow_add, hfermat, one_mul]
    have hx3 : ((a : ZMod p) ^ (p - 2)) ^ 3 = (a : ZMod p) ^ (p - 4) := by
      rw [← pow_mul, show (p - 2) * 3 = (p - 1) * 2 + (p - 4) by omega, pow_add, pow_mul,
        hfermat, one_pow, one_mul]
    have n01 : k0 ≠ k1 := by
      intro h; subst h
      exact pow_ne_zero (p - 2) ha0 (by linear_combination hk1 - hk0)
    have n02 : k0 ≠ k2 := by
      intro h; subst h
      exact pow_ne_zero (p - 3) ha0 (by linear_combination hk2 - hk0)
    have n03 : k0 ≠ k3 := by
      intro h; subst h
      exact pow_ne_zero (p - 4) ha0 (by linear_combination hk3 - hk0)
    have n12 : k1 ≠ k2 := by
      intro h; subst h
      have := hD2 (p - 2) (p - 3) (by omega) (by omega) (hk1.trans hk2.symm)
      omega
    have n13 : k1 ≠ k3 := by
      intro h; subst h
      have := hD2 (p - 2) (p - 4) (by omega) (by omega) (hk1.trans hk3.symm)
      omega
    have n23 : k2 ≠ k3 := by
      intro h; subst h
      have := hD2 (p - 3) (p - 4) (by omega) (by omega) (hk2.trans hk3.symm)
      omega
    have hA1 : (a : ZMod p) ^ (p - 2) = ((k1 : ZMod p) - k0) * (r : ZMod p) := by
      linear_combination hk1 - hk0
    have hB : ((a : ZMod p) ^ (p - 2)) ^ 2 = ((k2 : ZMod p) - k0) * (r : ZMod p) := by
      linear_combination hx2 + hk2 - hk0
    have hC : ((a : ZMod p) ^ (p - 2)) ^ 3 = ((k3 : ZMod p) - k0) * (r : ZMod p) := by
      linear_combination hx3 + hk3 - hk0
    have hw : ((k2 : ZMod p) - k0) = ((k1 : ZMod p) - k0) * ((a : ZMod p) ^ (p - 2)) := by
      have h1 : (r : ZMod p) * (((k2 : ZMod p) - k0) - ((k1 : ZMod p) - k0) *
          (a : ZMod p) ^ (p - 2)) = 0 := by
        linear_combination (-1 : ZMod p) * hB + (a : ZMod p) ^ (p - 2) * hA1
      exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hR)
    have hw2 : ((k3 : ZMod p) - k0) = ((k2 : ZMod p) - k0) * ((a : ZMod p) ^ (p - 2)) := by
      have h1 : (r : ZMod p) * (((k3 : ZMod p) - k0) - ((k2 : ZMod p) - k0) *
          (a : ZMod p) ^ (p - 2)) = 0 := by
        linear_combination (-1 : ZMod p) * hC + (a : ZMod p) ^ (p - 2) * hB
      exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hR)
    have hV : ((((k2 - k0) ^ 2 - (k1 - k0) * (k3 - k0) : ℤ)) : ZMod p) = 0 := by
      push_cast
      linear_combination ((k2 : ZMod p) - k0) * hw - ((k1 : ZMod p) - k0) * hw2
    have hdiv : (p : ℤ) ∣ (k2 - k0) ^ 2 - (k1 - k0) * (k3 - k0) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hV
    obtain ⟨b1, b2, b3⟩ := key k0 k1 k2 k3 hk0a hk0b hk1a hk1b hk2a hk2b hk3a hk3b
      n01 n02 n03 n12 n13 n23
    have h11z : (11 : ℤ) ≤ (p : ℤ) := by exact_mod_cast h11
    have hV0 := Int.eq_zero_of_abs_lt_dvd hdiv (by rw [abs_lt]; constructor <;> linarith)
    exact b3 hV0
  · rintro rfl
    refine ⟨by norm_num, by norm_num, 3, 1, by norm_num, by norm_num,
      fun n => if n = 1 then 2 else if n = 2 then 1 else 0, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro n hn
      simp only [Set.mem_Icc] at hn ⊢
      split_ifs <;> omega
    · intro m hm n hn hmn
      simp only [Set.mem_Icc] at hm hn
      dsimp only at hmn
      split_ifs at hmn <;> omega
    · intro j hj
      simp only [Set.mem_Icc] at hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact ⟨0, by norm_num, by norm_num⟩
      · exact ⟨2, by norm_num, by norm_num⟩
      · exact ⟨1, by norm_num, by norm_num⟩
    · rintro n ⟨h1, h2⟩
      interval_cases n <;> norm_num
