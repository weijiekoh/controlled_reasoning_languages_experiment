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
  rintro ⟨m, hm, hm0⟩
  by_cases h1 : a 1 = 0
  · exact Or.inl h1
  right
  have hper : ∀ n, a (n + m) = a n := by
    intro n
    induction n with
    | zero => simp [ha0, hm0]
    | succ n ih => rw [show n + 1 + m = (n + m) + 1 by omega, ha, ih, ha]
  have hK : ∀ K n, a (n + m * K) = a n := by
    intro K
    induction K with
    | zero => intro n; simp
    | succ K ih =>
      intro n
      rw [show n + m * (K + 1) = (n + m * K) + m by ring, hper, ih]
  have hdiv : ∀ n, (a (n+1) - a n) ∣ (a (n+2) - a (n+1)) := by
    intro n
    have h := Polynomial.sub_dvd_eval_sub (a (n+1)) (a n) f
    have e1 : a (n+1) = f.eval (a n) := ha n
    have e2 : a (n+2) = f.eval (a (n+1)) := ha (n+1)
    rw [← e1, ← e2] at h
    exact h
  have hchain : ∀ j k, j ≤ k → (a (j+1) - a j) ∣ (a (k+1) - a k) := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact dvd_refl _
    | succ k hk ih => exact dvd_trans ih (hdiv k)
  have hdown : ∀ j, (a (j+2) - a (j+1)) ∣ (a (j+1) - a j) := by
    intro j
    have h := hchain (j+1) (j+m) (by omega)
    have e : a (j+m+1) - a (j+m) = a (j+1) - a j := by
      rw [show j+m+1 = (j+1)+m by omega, hper, hper]
    rw [e] at h
    exact h
  have hsign : ∀ j, a (j+1) - a j = a (j+2) - a (j+1) ∨ a (j+1) - a j = -(a (j+2) - a (j+1)) := by
    intro j
    have h := Int.natAbs_eq_of_dvd_dvd (hdiv j) (hdown j)
    exact Int.natAbs_eq_natAbs_iff.mp h
  have key : ∃ j, a (j+2) = a j := by
    by_contra hno
    push_neg at hno
    have hall : ∀ j, a (j+1) - a j = a 1 - a 0 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        show a (j+2) - a (j+1) = a 1 - a 0
        rcases hsign j with h | h
        · linarith
        · exact absurd (by linarith : a (j+2) = a j) (hno j)
    have hlin : ∀ n : ℕ, a n = (n:ℤ) * a 1 := by
      intro n
      induction n with
      | zero => simp [ha0]
      | succ n ih =>
        have := hall n
        rw [ha0] at this
        push_cast
        linear_combination this + ih
    have hm' : (m:ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have e := hlin m
    rw [hm0] at e
    exact h1 ((mul_eq_zero.mp e.symm).resolve_left hm')
  obtain ⟨j, hj⟩ := key
  have fwd : ∀ i, j ≤ i → a (i+2) = a i := by
    intro i hi
    induction i, hi using Nat.le_induction with
    | base => exact hj
    | succ i hi ih =>
      have e1 : a (i+1+2) = f.eval (a (i+2)) := ha (i+2)
      have e2 : a (i+1) = f.eval (a i) := ha i
      rw [e1, ih, e2]
  have hL : j ≤ m * j := by nlinarith
  have A := fwd (m*j) hL
  have B : a (m*j) = a 0 := by
    have := hK j 0
    rwa [zero_add] at this
  have C : a (m*j+2) = a 2 := by
    have := hK j 2
    rwa [add_comm] at this
  rw [← C, A, B, ha0]
