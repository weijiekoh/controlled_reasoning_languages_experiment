import Mathlib

open Topology Filter

/--
Let $f(x)$ be a polynomial with integer coefficients. Define a sequence $a_0,a_1,\ldots$ of integers such that $a_0=0$ and $a_{n+1}=f(a_n)$ for all $n\geq 0$. Prove that if there exists a positive integer $m$ for which $a_m=0$ then either $a_1=0$ or $a_2=0$.
-/
theorem putnam_2000_a6
(f : Polynomial ℤ)
(a : ℕ → ℤ)
(ha0 : a 0 = 0)
(ha : ∀ n : ℕ, a (n + 1) = f.eval (a n))
: ((∃ m > 0, a m = 0) → (a 1 = 0 ∨ a 2 = 0)) := by
  classical
  intro hex0
  obtain ⟨m0, hm0pos, hm0⟩ := hex0
  have hex : ∃ m, 0 < m ∧ a m = 0 := ⟨m0, hm0pos, hm0⟩
  obtain ⟨m, hmpos, hmzero, hmin⟩ : ∃ m, 0 < m ∧ a m = 0 ∧ ∀ j, 0 < j → j < m → a j ≠ 0 :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun j hj0 hjm hj => Nat.find_min hex hjm ⟨hj0, hj⟩⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hd : ∀ n, a (n+1) - a n ∣ a (n+2) - a (n+1) := by
    intro n
    have h := Polynomial.sub_dvd_eval_sub (a (n+1)) (a n) f
    have h2' : a (n+2) = f.eval (a (n+1)) := ha (n+1)
    rw [← h2', ← ha n] at h
    exact h
  have hchain : ∀ i k, (a (i+1) - a i) ∣ (a (i+k+1) - a (i+k)) := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hd (i+k)
      have e1 : i + (k+1) + 1 = i+k+2 := by omega
      have e2 : i + (k+1) = i+k+1 := by omega
      rw [e1, e2]
      exact ih.trans h
  have hperiod : a (m+1) = a 1 := by
    rw [ha m, hmzero]
    have := ha 0
    rw [ha0] at this
    exact this.symm
  have hdm : a (m+1) - a m = a 1 := by rw [hperiod, hmzero, sub_zero]
  have hm_dvd : ∀ n, n ≤ m → a (n+1) - a n ∣ a 1 := by
    intro n hn
    have h := hchain n (m - n)
    have e : n + (m-n) + 1 = m+1 := by omega
    have e' : n + (m-n) = m := by omega
    rw [e, e', hdm] at h
    exact h
  have hc_dvd : ∀ n, a 1 ∣ a (n+1) - a n := by
    intro n
    have h := hchain 0 n
    simpa [ha0] using h
  have hdivsame : ∀ n, n ≤ m → a (n+1) - a n = a 1 ∨ a (n+1) - a n = -a 1 := by
    intro n hn
    have hab : (a (n+1) - a n).natAbs = (a 1).natAbs :=
      Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr (hm_dvd n hn))
        (Int.natAbs_dvd_natAbs.mpr (hc_dvd n))
    exact Int.natAbs_eq_natAbs_iff.mp hab
  have hwalk : ∀ n, 1 ≤ n → n < m → ∃ k : ℤ, 1 ≤ k ∧ a n = k * a 1 := by
    intro n
    induction n with
    | zero => intro h; exact absurd h (by norm_num)
    | succ n ih =>
      intro h1n hnm
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        exact ⟨1, le_refl _, by simp⟩
      · obtain ⟨k, hk1, hk⟩ := ih hnpos (by omega)
        rcases hdivsame n (by omega) with hs | hs
        · refine ⟨k+1, by omega, ?_⟩
          have e : a (n+1) = a n + a 1 := by linarith
          rw [e, hk]; ring
        · by_cases hk2 : k = 1
          · exfalso
            have e : a (n+1) = 0 := by
              have e' : a (n+1) = a n - a 1 := by linarith
              rw [e', hk, hk2]; ring
            exact hmin (n+1) (by omega) hnm e
          · refine ⟨k-1, by omega, ?_⟩
            have e : a (n+1) = a n - a 1 := by linarith
            rw [e, hk]; ring
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have : m = 1 := by omega
    rw [this] at hmzero
    exact h1 hmzero
  obtain ⟨k, hk1, hk⟩ := hwalk (m-1) (by omega) (by omega)
  have e : m - 1 + 1 = m := by omega
  have hsm := hdivsame (m-1) (by omega)
  rw [e, hk, hmzero] at hsm
  have hk1eq : k = 1 := by
    rcases hsm with h | h
    · exfalso
      have e2 : (k+1) * a 1 = 0 := by linear_combination -h
      rcases mul_eq_zero.mp e2 with h' | h'
      · omega
      · exact h1 h'
    · have e2 : (k-1) * a 1 = 0 := by linear_combination -h
      rcases mul_eq_zero.mp e2 with h' | h'
      · omega
      · exact absurd h' h1
  have hk_eq : a (m-1) = a 1 := by rw [hk, hk1eq, one_mul]
  have hfm : a m = f.eval (a (m-1)) := by
    have := ha (m-1)
    rwa [e] at this
  have h2e : a 2 = f.eval (a 1) := ha 1
  have hA : a m = f.eval (a 1) := by rw [hfm, hk_eq]
  exact h2 (by rw [h2e, ← hA, hmzero])
