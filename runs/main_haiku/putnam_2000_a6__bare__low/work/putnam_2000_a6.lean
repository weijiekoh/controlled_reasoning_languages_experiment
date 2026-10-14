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
  rintro ⟨m, hm, ham⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hper : ∀ k, a (k + m) = a k := by
    intro k
    induction k with
    | zero => simp [ha0, ham]
    | succ k ih =>
      rw [show k + 1 + m = (k + m) + 1 by ring, ha, ih, ← ha]
  have hperm : ∀ j k, a (k + m * j) = a k := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [show k + m * (j+1) = (k + m * j) + m by ring, hper, ih]
  have hdvd : ∀ n, (a (n+1) - a n) ∣ (a (n+1+1) - a (n+1)) := by
    intro n
    have := Polynomial.sub_dvd_eval_sub (a (n+1)) (a n) f
    rwa [← ha, ← ha] at this
  have hdvdk : ∀ n k, (a (n+1) - a n) ∣ (a (n+k+1) - a (n+k)) := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := hdvd (n+k)
      rw [show n + (k+1) + 1 = n+k+1+1 by ring, show n + (k+1) = n+k+1 by ring]
      exact dvd_trans ih h
  have hdvd2 : ∀ n, (a (n+1+1) - a (n+1)) ∣ (a (n+1) - a n) := by
    intro n
    have := hdvdk (n+1) (m-1)
    have e1 : a (n+1+(m-1)+1) = a (n+1) := by
      rw [show n+1+(m-1)+1 = (n+1)+m by omega, hper]
    have e2 : a (n+1+(m-1)) = a n := by
      rw [show n+1+(m-1) = n+m by omega, hper]
    rw [e1, e2] at this
    exact this
  have hnat : ∀ n, (a (n+1) - a n).natAbs = (a 1 - a 0).natAbs := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      exact ((Int.natAbs_eq_of_dvd_dvd (hdvd n) (hdvd2 n)).symm).trans ih
  have hpm : ∀ n, a (n+1) - a n = a 1 - a 0 ∨ a (n+1) - a n = -(a 1 - a 0) :=
    fun n => Int.natAbs_eq_natAbs_iff.mp (hnat n)
  have h1 : a 2 - a 1 = a 1 - a 0 ∨ a 2 - a 1 = -(a 1 - a 0) := hpm 1
  have h1' : a 2 - a 1 = a 1 := by omega
  by_cases hall : ∀ n, a (n+1) - a n = a 1 - a 0
  · have hlin : ∀ n : ℕ, a n = (n:ℤ) * a 1 := by
      intro n
      induction n with
      | zero => simp [ha0]
      | succ n ih =>
        have := hall n
        push_cast
        linear_combination this + ih - ha0
    have hm1 := hlin m
    rw [ham] at hm1
    rcases mul_eq_zero.mp hm1.symm with h | h
    · exact absurd h (by exact_mod_cast hm.ne')
    · exact hc1 h
  · push_neg at hall
    have hex := hall
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      have h0 : Nat.find hex ≠ 0 := by
        intro h
        have := Nat.find_spec hex
        rw [h] at this
        exact this (by simp)
      have h1ne : Nat.find hex ≠ 1 := by
        intro h
        have := Nat.find_spec hex
        rw [h] at this
        apply this
        show a 2 - a 1 = a 1 - a 0
        omega
      exact ⟨Nat.find hex - 1, by omega⟩
    have hkP : a (k+1) - a k = a 1 - a 0 := by
      have := Nat.find_min hex (show k < Nat.find hex by omega)
      push_neg at this
      exact this
    have hkP2 : a (k+1+1) - a (k+1) ≠ a 1 - a 0 := by
      have := Nat.find_spec hex
      rw [hk] at this
      exact this
    have hsign := hpm (k+1)
    have hd2 : a (k+1+1) - a (k+1) = -(a 1 - a 0) := by omega
    have hfx : Polynomial.eval (a k) f = a (k+1) := (ha k).symm
    have hfy : Polynomial.eval (a (k+1)) f = a (k+1+1) := (ha (k+1)).symm
    have hfy' : Polynomial.eval (a (k+1)) f = a k := by
      rw [hfy]; omega
    have hall2 : ∀ j, a (k+j) = a k ∨ a (k+j) = a (k+1) := by
      intro j
      induction j with
      | zero => left; simp
      | succ j ih =>
        rw [show k + (j+1) = (k+j)+1 by ring, ha]
        rcases ih with h | h
        · rw [h, hfx]; right; rfl
        · rw [h, hfy']; left; rfl
    obtain ⟨N, hN⟩ : ∃ N, N = m * (k+1) := ⟨_, rfl⟩
    have hperm' : ∀ t, a (t + N) = a t := by
      intro t; rw [hN]; exact hperm (k+1) t
    have hNk : k ≤ N := by rw [hN]; nlinarith
    have key : ∀ t, a t = a k ∨ a t = a (k+1) := by
      intro t
      have h2 := hall2 (t + N - k)
      rw [show k + (t + N - k) = t + N by omega, hperm'] at h2
      exact h2
    rcases key 0 with h0 | h0 <;> rcases key 1 with h1x | h1x <;>
      rcases key 2 with h2x | h2x <;> omega
