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
  rintro ⟨m, hm, ham⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  -- x - y ∣ f x - f y
  have hdiv : ∀ n, a (n+1) - a n ∣ a (n+1+1) - a (n+1) := by
    intro n
    have e := Polynomial.sub_dvd_eval_sub (a (n+1)) (a n) f
    rw [← ha n, ← ha (n+1)] at e
    exact e
  have hpair : ∀ n, a n - a 1 ∣ a (n+1) - a 2 := by
    intro n
    have e := Polynomial.sub_dvd_eval_sub (a n) (a 1) f
    have e1 : a 2 = f.eval (a 1) := ha 1
    rw [← ha n, ← e1] at e
    exact e
  have hchain : ∀ i k, a (i+1) - a i ∣ a (i+k+1) - a (i+k) := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      refine dvd_trans ih ?_
      have := hdiv (i+k)
      rw [show i + (k+1) + 1 = i+k+1+1 by omega, show i+(k+1) = i+k+1 by omega]
      exact this
  have e1 : a 1 = f.eval 0 := by
    have := ha 0
    simp only [zero_add, ha0] at this
    exact this
  have em : a (m+1) = f.eval 0 := by rw [ha m, ham]
  have hdm : a (m+1) - a m = a 1 := by
    rw [em, ham, e1]; simp
  have hsign : ∀ j, j ≤ m → a (j+1) - a j = a 1 ∨ a (j+1) - a j = -a 1 := by
    intro j hj
    have hA : a 1 - a 0 ∣ a (j+1) - a j := by
      have := hchain 0 j
      simpa using this
    have hB : a (j+1) - a j ∣ a (m+1) - a m := by
      have := hchain j (m-j)
      rwa [show j + (m-j) = m by omega] at this
    rw [ha0, sub_zero] at hA
    rw [hdm] at hB
    have := Int.natAbs_eq_of_dvd_dvd hA hB
    rcases Int.natAbs_eq_natAbs_iff.mp this with h | h
    · left; omega
    · right; omega
  rcases lt_or_gt_of_ne h1 with hneg | hpos
  · -- a 1 < 0: invariant a (k+1) ≤ a 1
    have key : ∀ k, k + 1 ≤ m → a (k+1) ≤ a 1 ∧ a 1 ∣ a (k+1) := by
      intro k
      induction k with
      | zero => intro _; exact ⟨le_refl _, dvd_refl _⟩
      | succ k ih =>
        intro hk
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hs := hsign (k+1) (by omega)
        have hd : a 1 ∣ a (k+1+1) := by
          have : a (k+1+1) = a (k+1) + (a (k+1+1) - a (k+1)) := by ring
          rw [this]
          refine dvd_add ih2 ?_
          rcases hs with h | h <;> rw [h] <;> simp
        refine ⟨?_, hd⟩
        rcases hs with hs | hs
        · have : a (k+1+1) = a (k+1) + a 1 := by linarith
          linarith
        · have hnext : a (k+1+1) = a (k+1) - a 1 := by linarith
          by_contra hlt
          push_neg at hlt
          obtain ⟨q, hq⟩ := ih2
          have hq1 : 2 ≤ q + 1 := by nlinarith
          have hq2 : 1 < q + 1 + 0 := by nlinarith
          have hq3 : q = 1 := by nlinarith
          subst hq3
          have hp := hpair (k+1)
          have h0 : a (k+1) - a 1 = 0 := by linarith
          rw [h0, zero_dvd_iff] at hp
          apply h2
          linarith
    have hk := key (m-1) (by omega)
    rw [show m-1+1 = m by omega, ham] at hk
    linarith [hk.1]
  · -- a 1 > 0: invariant a 1 ≤ a (k+1)
    have key : ∀ k, k + 1 ≤ m → a 1 ≤ a (k+1) ∧ a 1 ∣ a (k+1) := by
      intro k
      induction k with
      | zero => intro _; exact ⟨le_refl _, dvd_refl _⟩
      | succ k ih =>
        intro hk
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hs := hsign (k+1) (by omega)
        have hd : a 1 ∣ a (k+1+1) := by
          have : a (k+1+1) = a (k+1) + (a (k+1+1) - a (k+1)) := by ring
          rw [this]
          refine dvd_add ih2 ?_
          rcases hs with h | h <;> rw [h] <;> simp
        refine ⟨?_, hd⟩
        rcases hs with hs | hs
        · have : a (k+1+1) = a (k+1) + a 1 := by linarith
          linarith
        · have hnext : a (k+1+1) = a (k+1) - a 1 := by linarith
          by_contra hlt
          push_neg at hlt
          obtain ⟨q, hq⟩ := ih2
          have hq1 : 1 ≤ q := by nlinarith
          have hq2 : q < 2 := by nlinarith
          have hq3 : q = 1 := by omega
          subst hq3
          have hp := hpair (k+1)
          have h0 : a (k+1) - a 1 = 0 := by linarith
          rw [h0, zero_dvd_iff] at hp
          apply h2
          linarith
    have hk := key (m-1) (by omega)
    rw [show m-1+1 = m by omega, ham] at hk
    linarith [hk.1]
