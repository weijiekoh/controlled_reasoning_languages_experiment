import Mathlib

noncomputable abbrev putnam_2024_a4_solution : Set ℕ := {7}
theorem int_aux_p47 (p : ℤ) (hp : 11 ≤ p) (cl ci cj ck : ℤ) (hcl : -4 ≤ cl ∧ cl ≤ -1)
    (hci : -4 ≤ ci ∧ ci ≤ -1) (hcj : -4 ≤ cj ∧ cj ≤ -1) (hck : -4 ≤ ck ∧ ck ≤ -1)
    (c1 : cl ≠ ci) (c2 : cl ≠ cj) (c3 : cl ≠ ck) (c4 : ci ≠ cj) (c5 : ci ≠ ck) (c6 : cj ≠ ck)
    (hd : p ∣ (ci - cl) * (ck - cl) - (cj - cl) ^ 2) : False := by
  obtain ⟨a1, a2⟩ := hcl
  obtain ⟨b1, b2⟩ := hci
  obtain ⟨d1, d2⟩ := hcj
  obtain ⟨f1, f2⟩ := hck
  interval_cases cl <;> interval_cases ci <;> interval_cases cj <;> interval_cases ck <;>
    norm_num at hd ⊢ <;>
    first
    | omega
    | (have h := Int.le_of_dvd (by norm_num) hd; omega)
    | (have h := Int.le_of_dvd (by norm_num) (dvd_neg.mpr hd); omega)

theorem core_p47 (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (s R g : ZMod p) (hR : R ≠ 0)
    (hg0 : g ≠ 0) (hg1 : g ≠ 1) (hg2 : g ^ 2 ≠ 1) (cl ci cj ck : ℤ)
    (hcl : -4 ≤ cl ∧ cl ≤ -1) (hci : -4 ≤ ci ∧ ci ≤ -1) (hcj : -4 ≤ cj ∧ cj ≤ -1)
    (hck : -4 ≤ ck ∧ ck ≤ -1)
    (h0 : (0 : ZMod p) = s + (cl : ZMod p) * R) (h1 : g = s + (ci : ZMod p) * R)
    (h2 : g ^ 2 = s + (cj : ZMod p) * R) (h3 : g ^ 3 = s + (ck : ZMod p) * R) : False := by
  have dij : ∀ c c' : ℤ, ∀ x y : ZMod p, x = s + (c : ZMod p) * R →
      y = s + (c' : ZMod p) * R → x ≠ y → c ≠ c' := by
    intro c c' x y hx hy hxy hc
    apply hxy
    rw [hx, hy, hc]
  have n01 : (0 : ZMod p) ≠ g := fun h => hg0 h.symm
  have n02 : (0 : ZMod p) ≠ g ^ 2 := fun h => pow_ne_zero 2 hg0 h.symm
  have n03 : (0 : ZMod p) ≠ g ^ 3 := fun h => pow_ne_zero 3 hg0 h.symm
  have n12 : g ≠ g ^ 2 := by
    intro h
    have : g * (g - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hg0 h'
    · exact hg1 (by linear_combination h')
  have n13 : g ≠ g ^ 3 := by
    intro h
    have : g * (g ^ 2 - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hg0 h'
    · exact hg2 (by linear_combination h')
  have n23 : g ^ 2 ≠ g ^ 3 := by
    intro h
    have : g ^ 2 * (1 - g) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact pow_ne_zero 2 hg0 h'
    · exact hg1 (by linear_combination -h')
  have c1 := dij cl ci 0 g h0 h1 n01
  have c2 := dij cl cj 0 (g ^ 2) h0 h2 n02
  have c3 := dij cl ck 0 (g ^ 3) h0 h3 n03
  have c4 := dij ci cj g (g ^ 2) h1 h2 n12
  have c5 := dij ci ck g (g ^ 3) h1 h3 n13
  have c6 := dij cj ck (g ^ 2) (g ^ 3) h2 h3 n23
  obtain ⟨u, hu_def⟩ : ∃ u : ℤ, u = ci - cl := ⟨_, rfl⟩
  obtain ⟨v, hv_def⟩ : ∃ v : ℤ, v = cj - cl := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w : ℤ, w = ck - cl := ⟨_, rfl⟩
  have hu : g = (u : ZMod p) * R := by rw [hu_def]; push_cast; linear_combination h1 - h0
  have hv : g ^ 2 = (v : ZMod p) * R := by rw [hv_def]; push_cast; linear_combination h2 - h0
  have hw : g ^ 3 = (w : ZMod p) * R := by rw [hw_def]; push_cast; linear_combination h3 - h0
  have hV : (v : ZMod p) = (u : ZMod p) ^ 2 * R := by
    apply mul_right_cancel₀ hR
    rw [← hv, hu]; ring
  have hW : (w : ZMod p) = (u : ZMod p) * v * R := by
    apply mul_right_cancel₀ hR
    rw [← hw]
    have e3 : g ^ 3 = g * g ^ 2 := by ring
    rw [e3, hv, hu]; ring
  have hkey : (u : ZMod p) * w = (v : ZMod p) ^ 2 := by rw [hW, hV]; ring
  have hdvd : (p : ℤ) ∣ u * w - v ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hkey, sub_self]
  rw [hu_def, hv_def, hw_def] at hdvd
  exact int_aux_p47 (p : ℤ) (by exact_mod_cast hp) cl ci cj ck hcl hci hcj hck c1 c2 c3 c4 c5 c6 hdvd

theorem key_p47 (p : ℕ) [Fact p.Prime] (hp : 11 ≤ p) (a r : ℤ) (hr1 : 1 ≤ r)
    (hr2 : r ≤ (p : ℤ) - 1) (e : ℕ → ℕ)
    (hbij : Set.BijOn e (Set.Icc 0 (p - 5 : ℕ)) (Set.Icc 0 (p - 5 : ℕ)))
    (hdiv : ∀ n, 1 ≤ n ∧ n ≤ (p - 5 : ℕ) → (p : ℤ) ∣ a ^ (e n : ℕ) - a ^ (e (n - 1) : ℕ) - r) :
    False := by
  haveI : NeZero p := ⟨by omega⟩
  have hR : (r : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have := Int.le_of_dvd (by omega) h
    omega
  have hstep : ∀ n, 1 ≤ n → n ≤ p - 5 →
      (a : ZMod p) ^ (e n) - (a : ZMod p) ^ (e (n - 1)) - (r : ZMod p) = 0 := by
    intro n h1 h2
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hdiv n ⟨h1, h2⟩)
    push_cast at this
    exact this
  generalize (a : ZMod p) = A at hstep
  generalize (r : ZMod p) = R at hstep hR
  have hinjZ : ∀ n m : ℕ, n < p → m < p → (n : ZMod p) = (m : ZMod p) → n = m := by
    intro n m hn hm h
    have := (ZMod.natCast_eq_natCast_iff' n m p).mp h
    rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  obtain ⟨s, hs⟩ : ∃ s, A ^ (e 0) = s := ⟨_, rfl⟩
  have hAP : ∀ n, n ≤ p - 5 → A ^ (e n) = s + (n : ZMod p) * R := by
    intro n
    induction n with
    | zero => intro _; rw [Nat.cast_zero, zero_mul, add_zero]; exact hs
    | succ n ih =>
      intro hn
      have h1 := ih (by omega)
      have h2 := hstep (n + 1) (by omega) hn
      simp only [Nat.add_sub_cancel] at h2
      have h3 : A ^ (e (n + 1)) = A ^ (e n) + R := by linear_combination h2
      rw [h3, h1]; push_cast; ring
  have hsurj : ∀ k, k ≤ p - 5 → ∃ n, n ≤ p - 5 ∧ e n = k := by
    intro k hk
    obtain ⟨n, hn, hnk⟩ := hbij.surjOn (show k ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, hk⟩)
    exact ⟨n, hn.2, hnk⟩
  have hdistpow : ∀ i j, i ≤ p - 5 → j ≤ p - 5 → A ^ i = A ^ j → i = j := by
    intro i j hi hj hij
    obtain ⟨n, hn, rfl⟩ := hsurj i hi
    obtain ⟨m, hm, rfl⟩ := hsurj j hj
    rw [hAP n hn, hAP m hm] at hij
    have : (n : ZMod p) = (m : ZMod p) := mul_right_cancel₀ hR (add_left_cancel hij)
    rw [hinjZ n m (by omega) (by omega) this]
  have hA0 : A ≠ 0 := by
    intro h
    have hv : ∀ n, n ≤ p - 5 → s + (n : ZMod p) * R = 0 ∨ s + (n : ZMod p) * R = 1 := by
      intro n hn
      rw [← hAP n hn]
      rcases Nat.eq_zero_or_pos (e n) with h0 | h0
      · right; rw [h0, pow_zero]
      · left; rw [h, zero_pow h0.ne']
    have h1 := hv 0 (by omega)
    have h2 := hv 1 (by omega)
    have h3 := hv 2 (by omega)
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_mul, add_zero, one_mul] at h1 h2 h3
    have h2' : (2 : ZMod p) ≠ 0 := by
      intro h'
      have h'' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h'
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h''
      have := Int.le_of_dvd (by norm_num) h''
      omega
    have h2R : 2 * R ≠ 0 := mul_ne_zero h2' hR
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      first
      | exact hR (by linear_combination h2 - h1)
      | exact hR (by linear_combination h3 - h2)
      | exact h2R (by linear_combination h3 - h1)
  have hLpow : ∀ t, 1 ≤ t → t ≤ p - 2 → A ^ t ≠ 1 := by
    intro t ht1 ht2 ht
    by_cases hts : t ≤ p - 5
    · have := hdistpow t 0 hts (by omega) (by rw [ht, pow_zero])
      omega
    · have hfer : A ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hA0
      have hd : A ^ (Nat.gcd t (p - 1)) = 1 := pow_gcd_eq_one.mpr ⟨ht, hfer⟩
      have hdvd : Nat.gcd t (p - 1) ∣ (p - 1 - t) :=
        Nat.dvd_sub (Nat.gcd_dvd_right t (p - 1)) (Nat.gcd_dvd_left t (p - 1))
      have hle : Nat.gcd t (p - 1) ≤ p - 1 - t := Nat.le_of_dvd (by omega) hdvd
      have hpos : 0 < Nat.gcd t (p - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
      have := hdistpow (Nat.gcd t (p - 1)) 0 (by omega) (by omega) (by rw [hd, pow_zero])
      omega
  obtain ⟨g, hg⟩ : ∃ g, g = A⁻¹ := ⟨_, rfl⟩
  have hg0 : g ≠ 0 := by rw [hg]; exact inv_ne_zero hA0
  have hgA1 : g * A = 1 := by rw [hg]; exact inv_mul_cancel₀ hA0
  have hgm : ∀ m : ℕ, g ^ m * A ^ m = 1 := fun m => by rw [← mul_pow, hgA1, one_pow]
  have hcomp : ∀ m, 1 ≤ m → m ≤ 3 → ∀ n, n ≤ p - 5 → g ^ m ≠ s + (n : ZMod p) * R := by
    intro m hm1 hm3 n hn h
    have hen : e n ≤ p - 5 :=
      (hbij.mapsTo (show n ∈ Set.Icc 0 (p - 5) from ⟨Nat.zero_le _, hn⟩)).2
    have : A ^ (e n + m) = 1 := by
      rw [pow_add, hAP n hn, ← h]; exact hgm m
    exact hLpow (e n + m) (by omega) (by omega) this
  have cover : ∀ x : ZMod p, ∃ n, n < p ∧ x = s + (n : ZMod p) * R := by
    intro x
    have hf : Function.Injective (fun i : Fin p => s + ((i : ℕ) : ZMod p) * R) := by
      intro i j hij
      have h1 : ((i : ℕ) : ZMod p) * R = ((j : ℕ) : ZMod p) * R := add_left_cancel hij
      have h2 := mul_right_cancel₀ hR h1
      exact Fin.ext (hinjZ _ _ i.isLt j.isLt h2)
    have hbij' := (Fintype.bijective_iff_injective_and_card _).mpr ⟨hf, by simp [ZMod.card]⟩
    obtain ⟨i, hi⟩ := hbij'.2 x
    exact ⟨i, i.isLt, hi.symm⟩
  obtain ⟨l, hl, hl0⟩ := cover 0
  obtain ⟨i, hi, hi1⟩ := cover g
  obtain ⟨j, hj, hj2⟩ := cover (g ^ 2)
  obtain ⟨k, hk, hk3⟩ := cover (g ^ 3)
  have hl' : p - 4 ≤ l := by
    by_contra hc
    exact pow_ne_zero (e l) hA0 (by rw [hAP l (by omega), ← hl0])
  have hi' : p - 4 ≤ i := by
    by_contra hc
    exact hcomp 1 le_rfl (by norm_num) i (by omega) (by rw [pow_one]; exact hi1)
  have hj' : p - 4 ≤ j := by
    by_contra hc
    exact hcomp 2 (by norm_num) (by norm_num) j (by omega) hj2
  have hk' : p - 4 ≤ k := by
    by_contra hc
    exact hcomp 3 (by norm_num) (by norm_num) k (by omega) hk3
  have hg1 : g ≠ 1 := by
    intro h
    apply hLpow 1 le_rfl (by omega)
    rw [pow_one]
    rw [h, one_mul] at hgA1
    exact hgA1
  have hg2 : g ^ 2 ≠ 1 := by
    intro h
    apply hLpow 2 (by norm_num) (by omega)
    have := hgm 2
    rw [h, one_mul] at this
    exact this
  have hc : ∀ n : ℕ, ((((n : ℤ) - p : ℤ)) : ZMod p) = (n : ZMod p) := by
    intro n; push_cast; simp
  exact core_p47 p hp s R g hR hg0 hg1 hg2 ((l : ℤ) - p) ((i : ℤ) - p) ((j : ℤ) - p) ((k : ℤ) - p)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by rw [hc l]; exact hl0) (by rw [hc i]; exact hi1) (by rw [hc j]; exact hj2)
    (by rw [hc k]; exact hk3)

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
      by_contra hc
      interval_cases p <;> first | exact absurd rfl hne | (norm_num at hp)
    haveI := Fact.mk hp
    exact key_p47 p h11 a r hr1 hr2 e hbij hdiv
  · rintro rfl
    refine ⟨by norm_num, by norm_num, 3, 1, le_refl _, by norm_num,
      fun n => if n = 1 then 2 else if n = 2 then 1 else 0, ?_, ?_⟩
    · show Set.BijOn _ (Set.Icc 0 2) (Set.Icc 0 2)
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨hx1, hx2⟩ := hx
        interval_cases x <;> simp
      · intro x hx y hy hxy
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨hy1, hy2⟩ := hy
        interval_cases x <;> interval_cases y <;> simp_all
      · intro y hy
        obtain ⟨hy1, hy2⟩ := hy
        interval_cases y
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨2, by simp, by simp⟩
        · exact ⟨1, by simp, by simp⟩
    · intro n hn
      obtain ⟨h1, h2⟩ := hn
      interval_cases n <;> norm_num
