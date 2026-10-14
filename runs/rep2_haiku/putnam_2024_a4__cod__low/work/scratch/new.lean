import Mathlib

noncomputable abbrev putnam_2024_a4_solution : Set ℕ := {7}

lemma fin_aux (a0 b1 b2 b3 D : ℤ) (ha0 : 0 ≤ a0) (ha3 : a0 ≤ 3)
    (hb1 : 0 ≤ b1) (hb1' : b1 ≤ 3) (hb2 : 0 ≤ b2) (hb2' : b2 ≤ 3)
    (hb3 : 0 ≤ b3) (hb3' : b3 ≤ 3)
    (h12 : b1 ≠ b2) (h13 : b1 ≠ b3) (h23 : b2 ≠ b3)
    (h1 : b1 ≠ a0) (h2 : b2 ≠ a0) (h3 : b3 ≠ a0)
    (hD : D = (b2 - a0)^2 - (b1 - a0) * (b3 - a0)) :
    -7 ≤ D ∧ D ≤ 7 ∧ D ≠ 0 := by
  subst hD
  interval_cases a0 <;> interval_cases b1 <;> interval_cases b2 <;> interval_cases b3 <;>
    norm_num at *

lemma key_no (p : ℕ) (hp : p.Prime) (hp11 : 11 ≤ p) (A R : ZMod p) (hR : R ≠ 0)
    (e : ℕ → ℕ) (he : Set.BijOn e (Set.Icc 0 (p - 5 : ℕ)) (Set.Icc 0 (p - 5 : ℕ)))
    (hrec : ∀ n, 1 ≤ n → n ≤ p - 5 → A ^ (e n) - A ^ (e (n-1)) = R) : False := by
  haveI := Fact.mk hp
  have hp11' : (11 : ℤ) ≤ p := by exact_mod_cast hp11
  obtain ⟨w, hw⟩ : ∃ w : ZMod p, w = A ^ (e 0) := ⟨_, rfl⟩
  have hform : ∀ n, n ≤ p - 5 → A ^ (e n) = w + (n : ZMod p) * R := by
    intro n
    induction n with
    | zero => intro _; simp [hw]
    | succ k ih =>
      intro hk
      have h1 := hrec (k+1) (by omega) hk
      simp only [Nat.add_sub_cancel] at h1
      have h2 := ih (by omega)
      push_cast
      linear_combination h1 + h2
  have hcast_inj : ∀ m n : ℕ, m < p → n < p → (m : ZMod p) * R = (n : ZMod p) * R → m = n := by
    intro m n hm hn h
    have h2 : (m : ZMod p) = (n : ZMod p) := mul_right_cancel₀ hR h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h2
    exact h2
  have hgInj : ∀ k1 k2, k1 ≤ p - 5 → k2 ≤ p - 5 → A ^ k1 = A ^ k2 → k1 = k2 := by
    intro k1 k2 h1 h2 hA
    obtain ⟨n1, hn1, hn1e⟩ := he.surjOn (show k1 ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, h1⟩)
    obtain ⟨n2, hn2, hn2e⟩ := he.surjOn (show k2 ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, h2⟩)
    have h3 : w + (n1 : ZMod p) * R = w + (n2 : ZMod p) * R := by
      rw [← hform n1 hn1.2, ← hform n2 hn2.2, hn1e, hn2e, hA]
    have : n1 = n2 := hcast_inj n1 n2 (by have := hn1.2; omega) (by have := hn2.2; omega)
      (add_left_cancel h3)
    rw [← hn1e, ← hn2e, this]
  have hA0 : A ≠ 0 := by
    intro h0
    have := hgInj 1 2 (by omega) (by omega) (by rw [h0]; simp)
    omega
  have hfermat : A ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hA0
  have hdvd : orderOf A ∣ p - 1 := orderOf_dvd_of_pow_eq_one hfermat
  have hpos : 0 < orderOf A := by
    rcases Nat.eq_zero_or_pos (orderOf A) with h0 | h0
    · rw [h0, zero_dvd_iff] at hdvd; omega
    · exact h0
  have hge : p - 4 ≤ orderOf A := by
    by_contra hlt
    push_neg at hlt
    have := hgInj (orderOf A) 0 (by omega) (by omega) (by rw [pow_orderOf_eq_one, pow_zero])
    omega
  have hd_eq : orderOf A = p - 1 := by
    obtain ⟨m, hm⟩ := hdvd
    generalize orderOf A = d at hm hge hpos ⊢
    rcases m with _ | _ | m
    · omega
    · omega
    · exfalso
      have h2 : d * (m + 1 + 1) ≥ d * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
  have hlt_inj : ∀ j k, j < k → k ≤ p - 2 → A ^ j ≠ A ^ k := by
    intro j k hjk hk heq
    have h1 : A ^ k = A ^ j * A ^ (k - j) := by
      rw [← pow_add]; congr 1; omega
    have h2 : A ^ (k - j) = 1 := by
      have : A ^ j * A ^ (k - j) = A ^ j * 1 := by rw [← h1, mul_one, heq]
      exact mul_left_cancel₀ (pow_ne_zero _ hA0) this
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hd_eq] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  have hgInj2 : ∀ j k, j ≤ p - 2 → k ≤ p - 2 → A ^ j = A ^ k → j = k := by
    intro j k hj hk h
    rcases lt_trichotomy j k with h' | h' | h'
    · exact absurd h (hlt_inj j k h' hk)
    · exact h'
    · exact absurd h.symm (hlt_inj k j h' hj)
  have hsurj : ∀ x : ZMod p, ∃ n : ℕ, n < p ∧ w + (n : ZMod p) * R = x := by
    intro x
    refine ⟨((x - w) * R⁻¹).val, ZMod.val_lt _, ?_⟩
    rw [ZMod.natCast_zmod_val]
    have : (x - w) * R⁻¹ * R = x - w := by field_simp
    linear_combination this
  have hidx : ∀ i, p - 4 ≤ i → i ≤ p - 2 →
      ∃ n, p - 4 ≤ n ∧ n < p ∧ w + (n : ZMod p) * R = A ^ i := by
    intro i hi1 hi2
    obtain ⟨n, hnp, hn⟩ := hsurj (A ^ i)
    refine ⟨n, ?_, hnp, hn⟩
    by_contra hlt
    push_neg at hlt
    have hle : n ≤ p - 5 := by omega
    have heq : A ^ (e n) = A ^ i := (hform n hle).trans hn
    have hmem := he.mapsTo (show n ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, hle⟩)
    have := hgInj2 (e n) i (by have := hmem.2; omega) hi2 heq
    have := hmem.2
    omega
  obtain ⟨n0, hn0p, hn0⟩ := hsurj 0
  have hn0ge : p - 4 ≤ n0 := by
    by_contra hlt
    push_neg at hlt
    have hle : n0 ≤ p - 5 := by omega
    exact pow_ne_zero (e n0) hA0 ((hform n0 hle).trans hn0)
  obtain ⟨n1, hn1a, hn1p, hn1⟩ := hidx (p-4) le_rfl (by omega)
  obtain ⟨n2, hn2a, hn2p, hn2⟩ := hidx (p-3) (by omega) (by omega)
  obtain ⟨n3, hn3a, hn3p, hn3⟩ := hidx (p-2) (by omega) le_rfl
  have hne12 : n1 ≠ n2 := by
    rintro rfl
    have := hgInj2 (p-4) (p-3) (by omega) (by omega) (hn1.symm.trans hn2)
    omega
  have hne13 : n1 ≠ n3 := by
    rintro rfl
    have := hgInj2 (p-4) (p-2) (by omega) (by omega) (hn1.symm.trans hn3)
    omega
  have hne23 : n2 ≠ n3 := by
    rintro rfl
    have := hgInj2 (p-3) (p-2) (by omega) (by omega) (hn2.symm.trans hn3)
    omega
  have hn10 : n1 ≠ n0 := by
    intro h
    subst h
    exact pow_ne_zero (p-4) hA0 (by rw [← hn1, hn0])
  have hn20 : n2 ≠ n0 := by
    intro h
    subst h
    exact pow_ne_zero (p-3) hA0 (by rw [← hn2, hn0])
  have hn30 : n3 ≠ n0 := by
    intro h
    subst h
    exact pow_ne_zero (p-2) hA0 (by rw [← hn3, hn0])
  have hgeo : A ^ (p-3) * A ^ (p-3) = A ^ (p-4) * A ^ (p-2) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hsq : (w + (n2 : ZMod p) * R) * (w + (n2 : ZMod p) * R)
      = (w + (n1 : ZMod p) * R) * (w + (n3 : ZMod p) * R) := by
    rw [hn1, hn2, hn3]; exact hgeo
  have hD : R ^ 2 * (((n2 : ZMod p) - n0) ^ 2
      - ((n1 : ZMod p) - n0) * ((n3 : ZMod p) - n0)) = 0 := by
    linear_combination hsq - (2 * ((n2 : ZMod p) - n0) * R - ((n1 : ZMod p) - n0) * R
      - ((n3 : ZMod p) - n0) * R) * hn0
  have hD0 : ((n2 : ZMod p) - n0) ^ 2 - ((n1 : ZMod p) - n0) * ((n3 : ZMod p) - n0) = 0 := by
    rcases mul_eq_zero.mp hD with h | h
    · exact absurd h (pow_ne_zero 2 hR)
    · exact h
  have hZ : ((((n2 : ℤ) - n0) ^ 2 - ((n1 : ℤ) - n0) * ((n3 : ℤ) - n0) : ℤ) : ZMod p) = 0 := by
    push_cast; exact hD0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hZ
  obtain ⟨c, hc⟩ := hZ
  have hfin := fin_aux ((n0 : ℤ) - ((p - 4 : ℕ) : ℤ)) ((n1 : ℤ) - ((p - 4 : ℕ) : ℤ))
    ((n2 : ℤ) - ((p - 4 : ℕ) : ℤ)) ((n3 : ℤ) - ((p - 4 : ℕ) : ℤ))
    (((n2 : ℤ) - n0) ^ 2 - ((n1 : ℤ) - n0) * ((n3 : ℤ) - n0))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by ring)
  obtain ⟨f1, f2, f3⟩ := hfin
  have hc0 : c = 0 := by
    rcases lt_trichotomy c 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  exact f3 (by rw [hc, hc0, mul_zero])

theorem putnam_2024_a4 :
    {p : ℕ | p.Prime ∧ 5 < p ∧ ∃ a r : ℤ, 1 ≤ r ∧ r ≤ p - 1 ∧
      ∃ e : ℕ → ℕ, Set.BijOn e (Set.Icc 0 (p - 5 : ℕ)) (Set.Icc 0 (p - 5 : ℕ)) ∧
        ∀ n, 1 ≤ n ∧ n ≤ (p - 5 : ℕ) →
          (p : ℤ) ∣ a ^ (e n : ℕ) - a ^ (e (n - 1) : ℕ) - r} =
    putnam_2024_a4_solution := by
  ext p
  simp only [putnam_2024_a4_solution, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hp5, a, r, hr1, hr2, e, he, hrec⟩
    by_contra hne
    have hp11 : 11 ≤ p := by
      by_contra h
      push_neg at h
      interval_cases p <;> first | omega | (norm_num at hp)
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hR : (r : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      have := Int.le_of_dvd (by omega) h0
      omega
    have hrec' : ∀ n, 1 ≤ n → n ≤ p - 5 →
        (a : ZMod p) ^ (e n) - (a : ZMod p) ^ (e (n-1)) = (r : ZMod p) := by
      intro n h1 h2
      have h := hrec n ⟨h1, h2⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      push_cast at h
      linear_combination h
    exact key_no p hp hp11 (a : ZMod p) (r : ZMod p) hR e he hrec'
  · rintro rfl
    refine ⟨by norm_num, by norm_num, 3, 1, by norm_num, by norm_num,
      fun n => if n = 1 then 2 else if n = 2 then 1 else 0, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx
        have hx2 : x ≤ 2 := by simp only [Set.mem_Icc] at hx; omega
        interval_cases x <;> simp [Set.mem_Icc]
      · intro x hx y hy hxy
        have hx2 : x ≤ 2 := by simp only [Set.mem_Icc] at hx; omega
        have hy2 : y ≤ 2 := by simp only [Set.mem_Icc] at hy; omega
        interval_cases x <;> interval_cases y <;> simp_all
      · intro y hy
        have hy2 : y ≤ 2 := by simp only [Set.mem_Icc] at hy; omega
        interval_cases y
        · exact ⟨0, by simp [Set.mem_Icc], by simp⟩
        · exact ⟨2, by simp [Set.mem_Icc], by simp⟩
        · exact ⟨1, by simp [Set.mem_Icc], by simp⟩
    · rintro n ⟨h1, h2⟩
      have h3 : n ≤ 2 := by norm_num at h2; omega
      interval_cases n <;> norm_num
