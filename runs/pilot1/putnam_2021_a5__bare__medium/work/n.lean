import Mathlib

open Filter Topology

lemma key (p : ℕ) [Fact p.Prime] (hp : p ∣ 2021) (g : ℕ) (hg : Nat.Coprime g 2021)
    (hord : ∀ r < p - 1, ((g : ZMod p))^r = 1 → r = 0) (hcard : ((1932 : ℕ) : ZMod p) ≠ 0)
    (A : Finset ℕ) (hm : ∀ n, n ∈ A ↔ 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1) (j : ℕ) :
    (p ∣ ∑ n ∈ A, n ^ j) ↔ ¬ (p - 1) ∣ j := by
  have hAeq : A = (Finset.Icc 1 2021).filter (fun n => n.gcd 2021 = 1) := by
    ext n; rw [hm]; simp [and_assoc]
  have hcA : A.card = 1932 := by
    rw [hAeq]; decide +kernel
  have hpc : ∀ n ∈ A, Nat.Coprime n p := by
    intro n hn
    exact Nat.Coprime.coprime_dvd_right hp ((hm n).1 hn).2.2
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h hd
    obtain ⟨k, rfl⟩ := hd
    have : ∀ n ∈ A, ((n : ZMod p))^((p-1)*k) = 1 := by
      intro n hn
      have h0 : (n : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.Coprime.eq_one_of_dvd (hpc n hn).symm hd
        exact (Fact.out : p.Prime).one_lt.ne' this
      rw [pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow]
    rw [Finset.sum_congr rfl this] at h
    simp [hcA] at h
    exact hcard (by exact_mod_cast h)
  · intro hd
    have hlt : ∀ a ∈ A, a < 2021 := by
      intro a ha
      have ha' := (hm a).1 ha
      rcases lt_or_eq_of_le ha'.2.1 with h | h
      · exact h
      · subst h; simp at ha'
    have hinj : Set.InjOn (fun n => (g * n) % 2021) (A : Set ℕ) := by
      intro a ha b hb hab
      have h1 : g * a ≡ g * b [MOD 2021] := hab
      have h2 := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.gcd_comm] using hg) h1
      exact Nat.ModEq.eq_of_lt_of_lt h2 (hlt a ha) (hlt b hb)
    have hmaps : ∀ n ∈ A, (g * n) % 2021 ∈ A := by
      intro n hn
      have hn' := (hm n).1 hn
      have hc : Nat.gcd ((g * n) % 2021) 2021 = 1 := by
        have : Nat.Coprime (g * n) 2021 := Nat.Coprime.mul_left hg hn'.2.2
        have h3 := Nat.gcd_rec 2021 (g * n)
        rw [Nat.gcd_comm] at h3
        rw [← h3]; exact this
      rw [hm]
      refine ⟨?_, (Nat.mod_lt _ (by norm_num)).le, hc⟩
      rcases Nat.eq_zero_or_pos ((g * n) % 2021) with h | h
      · rw [h] at hc; simp at hc
      · exact h
    have himg : A.image (fun n => (g * n) % 2021) = A := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
        exact hmaps n hn
      · rw [Finset.card_image_of_injOn hinj]
    set T : ZMod p := ∑ n ∈ A, (n : ZMod p) ^ j with hT
    have hshift : T = (g : ZMod p) ^ j * T := by
      conv_lhs => rw [hT, ← himg]
      rw [Finset.sum_image hinj, hT, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have : (((g * n) % 2021 : ℕ) : ZMod p) = (g : ZMod p) * n := by
        rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 ((Nat.mod_modEq _ _).of_dvd hp)]
        push_cast; rfl
      simp only [this, mul_pow]
    have hg0 : (g : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hp hg).symm hd
      exact (Fact.out : p.Prime).one_lt.ne' this
    have hne : (g : ZMod p) ^ j ≠ 1 := by
      intro h1
      apply hd
      have hp1 : (g : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hg0
      have : (g : ZMod p) ^ (j % (p - 1)) = 1 := by
        rw [← Nat.mod_add_div j (p - 1), pow_add, pow_mul, hp1, one_pow, mul_one] at h1
        exact h1
      have hr := hord _ (Nat.mod_lt _ (by have := (Fact.out : p.Prime).two_le; omega)) this
      exact Nat.dvd_of_mod_eq_zero hr
    have : ((g : ZMod p) ^ j - 1) * T = 0 := by
      rw [sub_mul, ← hshift]; simp
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

lemma o43 : ∀ r < 43 - 1, ((3 : ℕ) : ZMod 43)^r = 1 → r = 0 := by decide +kernel
lemma o47 : ∀ r < 47 - 1, ((5 : ℕ) : ZMod 47)^r = 1 → r = 0 := by decide +kernel

noncomputable abbrev putnam_2021_a5_solution : Set ℕ := {j : ℕ | ¬(42 ∣ j) ∧ ¬(46 ∣ j)}
/--
Let $A$ be the set of all integers $n$ such that $1 \leq n \leq 2021$ and $\gcd(n,2021)=1$. For every nonnegative integer $j$, let $S(j)=\sum_{n \in A}n^j$. Determine all values of $j$ such that $S(j)$ is a multiple of $2021$.
-/
theorem putnam_2021_a5
  (j : ℕ)
  (A : Finset ℕ)
  (S : ℕ → ℕ)
  (hA : A = {n | 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1})
  (hS : ∀ j' : ℕ, S j' = ∑ n ∈ A, n ^ j') :
  (2021 ∣ S j) ↔ j ∈ putnam_2021_a5_solution := by
  have hm : ∀ n, n ∈ A ↔ 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1 := fun n => by
    have := Set.ext_iff.1 hA n
    simpa using this
  have c43 : ((1932 : ℕ) : ZMod 43) ≠ 0 := by decide
  have c47 : ((1932 : ℕ) : ZMod 47) ≠ 0 := by decide
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 47) := ⟨by norm_num⟩
  have k43 := key 43 (by norm_num) 3 (by norm_num) o43 c43 A hm j
  have k47 := key 47 (by norm_num) 5 (by norm_num) o47 c47 A hm j
  rw [hS]
  simp only [putnam_2021_a5_solution, Set.mem_setOf_eq]
  constructor
  · intro h
    have h1 : 43 ∣ ∑ n ∈ A, n ^ j := dvd_trans ⟨47, by norm_num⟩ h
    have h2 : 47 ∣ ∑ n ∈ A, n ^ j := dvd_trans ⟨43, by norm_num⟩ h
    exact ⟨by simpa using k43.1 h1, by simpa using k47.1 h2⟩
  · rintro ⟨h1, h2⟩
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 43 47)
      (k43.2 (by simpa using h1)) (k47.2 (by simpa using h2))
    simpa using this
