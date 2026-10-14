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
: ((∃ m > 0, a m = 0) → (a 1 = 0 ∨ a 2 = 0)) :=
by
  classical
  rintro ⟨m, hm, ham⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨d, hd⟩ : ∃ d : ℕ → ℤ, ∀ i, d i = a (i+1) - a i := ⟨_, fun i => rfl⟩
  have hper : ∀ x, a (x+m) = a x := by
    intro x
    induction x with
    | zero => simp [ham, ha0]
    | succ n ih =>
      rw [show n+1+m = (n+m)+1 by ring, ha, ih, ha]
  have hper2 : ∀ x s, a (x + m*s) = a x := by
    intro x s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [show x + m*(s+1) = (x + m*s) + m by ring, hper, ih]
  have hdiv : ∀ i, d i ∣ d (i+1) := by
    intro i
    have := Polynomial.sub_dvd_eval_sub (a (i+1)) (a i) f
    rw [← ha i] at this
    rw [hd, hd, ha (i+1)]
    exact this
  have hchain : ∀ i j, i ≤ j → d i ∣ d j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact dvd_refl _
    | succ n _ ih => exact ih.trans (hdiv n)
  have hdper : ∀ x, d (x+m) = d x := by
    intro x
    rw [hd, hd, show x+m+1 = x+1+m by ring, hper, hper]
  have hdperk : ∀ r s, d (r + m*s) = d r := by
    intro r s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [show r + m*(s+1) = (r + m*s) + m by ring, hdper, ih]
  have hdm : d m = d 0 := by simpa using hdper 0
  have hdall : ∀ j, d j ∣ d 0 := by
    intro j
    have hj : d j = d (j % m) := by
      conv_lhs => rw [← Nat.mod_add_div j m]
      rw [hdperk]
    rw [hj, ← hdm]
    exact hchain _ _ (Nat.le_of_lt (Nat.mod_lt _ hm))
  have hdall2 : ∀ j, d 0 ∣ d j := fun j => hchain 0 j (Nat.zero_le j)
  have hsign : ∀ j, d j = d 0 ∨ d j = -d 0 := by
    intro j
    have h : (d j).natAbs = (d 0).natAbs :=
      Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.2 (hdall j)) (Int.natAbs_dvd_natAbs.2 (hdall2 j))
    exact Int.natAbs_eq_natAbs_iff.1 h
  have e0 := hd 0
  have e1 := hd 1
  norm_num at e0 e1
  have hd0 : d 0 ≠ 0 := by
    rw [e0, ha0]; simpa using h1
  have hd1 : d 1 ≠ -d 0 := by
    intro h
    apply h2
    rw [e0, ha0] at h
    rw [e1] at h
    linarith
  -- values of a at all n if all differences equal d 0
  have hvals : (∀ j, d j = d 0) → False := by
    intro hall
    have hform : ∀ n : ℕ, a n = (n : ℤ) * d 0 := by
      intro n
      induction n with
      | zero => simp [ha0]
      | succ n ih =>
        have h' := hd n
        rw [hall n] at h'
        push_cast
        linarith
    have := hform m
    rw [ham] at this
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    rcases mul_eq_zero.1 this.symm with h | h
    · exact hm' h
    · exact hd0 h
  have hex : ∃ j, d j = -d 0 := by
    by_contra hne
    push_neg at hne
    exact hvals (fun j => (hsign j).resolve_right (hne j))
  obtain ⟨j, hj, hmin⟩ : ∃ j, d j = -d 0 ∧ ∀ i < j, d i ≠ -d 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  -- find a sign change at index k with a (k+2) = a k
  have hk : ∃ k, a (k+2) = a k := by
    match j, hj, hmin with
    | 0, hj, _ => exact absurd hj (by intro h; apply hd0; linarith)
    | 1, hj, _ => exact absurd hj hd1
    | i+2, hj, hmin =>
      have hi1 : d (i+1) = d 0 := (hsign (i+1)).resolve_right (hmin (i+1) (by omega))
      refine ⟨i+1, ?_⟩
      have f1 := hd (i+1)
      have f2 := hd (i+1+1)
      have f3 := hd (i+1)
      rw [hi1] at f1
      have : a (i+1+1+1) = a (i+1) := by
        have := hj
        rw [show i+2 = i+1+1 from rfl] at this
        rw [f2] at this
        linarith
      rw [show i+1+2 = i+1+1+1 by ring]
      exact this
  obtain ⟨k, hk⟩ := hk
  have hev : ∀ n, a (k+n+2) = a (k+n) := by
    intro n
    induction n with
    | zero => simpa using hk
    | succ n ih =>
      have e2 : a (k+(n+1)+2) = f.eval (a (k+n+2)) := by
        rw [show k+(n+1)+2 = (k+n+2)+1 by ring]; exact ha _
      have e3 : a (k+(n+1)) = f.eval (a (k+n)) := by
        rw [show k+(n+1) = (k+n)+1 by ring]; exact ha _
      rw [e2, e3, ih]
  have hkm : k ≤ m*k := by nlinarith
  obtain ⟨n, hn⟩ : ∃ n, m*k = k + n := ⟨m*k - k, by omega⟩
  have h2eq : a 2 = a 0 := by
    calc a 2 = a (2 + m*k) := (hper2 2 k).symm
    _ = a (k + n + 2) := by congr 1; omega
    _ = a (k + n) := hev n
    _ = a (0 + m*k) := by congr 1; omega
    _ = a 0 := hper2 0 k
  exact h2 (h2eq.trans ha0)
