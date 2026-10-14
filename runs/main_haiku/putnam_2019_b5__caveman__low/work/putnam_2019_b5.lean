import Mathlib

open Topology Filter Set Matrix

noncomputable abbrev putnam_2019_b5_solution : ℕ × ℕ := ⟨2019, 1010⟩
/--
Let $F_m$ be the $m$th Fibonacci number, defined by $F_1 = F_2 = 1$ and $F_m = F_{m-1} + F_{m-2}$ for all $m \geq 3$. Let $p(x)$ be the polynomial of degree $1008$ such that $p(2n + 1) = F_{2n+1}$ for $n = 0,1,2,\ldots,1008$. Find integers $j$ and $k$ such that $p(2019) = F_j - F_k$.
-/
theorem putnam_2019_b5
(F : ℕ → ℤ)
(P : Polynomial ℝ)
(hF : ∀ x, x ≥ 1 → F (x + 2) = F (x + 1) + F x)
(F12 : F 1 = 1 ∧ F 2 = 1)
(Pdeg: Polynomial.degree P = 1008)
(hp: ∀ n : ℕ, (n ≤ 1008) → P.eval (2 * n + 1 : ℝ) = F (2 * n + 1))
: ∀ j k : ℕ, (P.eval 2019 = F j - F k ∧ 1 ≤ j ∧ 1 ≤ k) ↔ ⟨j, k⟩ = putnam_2019_b5_solution  := by
  classical
  -- Fibonacci identification: F n = Nat.fib n for n ≥ 1
  have hFib : ∀ n : ℕ, F (n+1) = (Nat.fib (n+1) : ℤ) ∧ F (n+2) = (Nat.fib (n+2) : ℤ) := by
    intro n
    induction n with
    | zero => simp [F12.1, F12.2, Nat.fib_one, Nat.fib_two]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h3 := hF (n+1) (by omega)
      have h5 : F (n+1+1) = (Nat.fib (n+1+1) : ℤ) := ih.2
      have h4 : Nat.fib (n+1+2) = Nat.fib (n+1) + Nat.fib (n+1+1) := Nat.fib_add_two
      have h6 : (Nat.fib (n+1+2) : ℤ) = (Nat.fib (n+1) : ℤ) + (Nat.fib (n+1+1) : ℤ) := by
        rw [h4]; push_cast; ring
      rw [h6, h3, h5, ih.1]; ring
  have hFibF : ∀ n : ℕ, 1 ≤ n → F n = (Nat.fib n : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (hFib m).1
  -- degree of P
  have hPdeg : P.natDegree = 1008 := Polynomial.natDegree_eq_of_degree_eq_some Pdeg
  -- Q(k) = P(2k+1)
  set Q : Polynomial ℝ := P.comp (Polynomial.C 2 * Polynomial.X + Polynomial.C 1) with hQ
  have hQdeg : Q.natDegree < 1009 := by
    rw [hQ]
    have h1 : (Polynomial.C (2:ℝ) * Polynomial.X + Polynomial.C 1).natDegree ≤ 1 := by
      apply (Polynomial.natDegree_add_le _ _).trans
      simp
    have := Polynomial.natDegree_comp_le (p := P) (q := Polynomial.C (2:ℝ) * Polynomial.X + Polynomial.C 1)
    rw [hPdeg] at this
    nlinarith
  have hQeval : ∀ x : ℝ, Q.eval x = P.eval (2 * x + 1) := by
    intro x
    simp [hQ, Polynomial.eval_comp]
  -- finite difference vanishing
  have hzero := Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := Q) (n := 1009) hQdeg
  have hpt := congrFun hzero 0
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range_succ] at hpt
  simp only [zero_add, nsmul_eq_mul, mul_one] at hpt
  -- finite difference identity at the point 2019
  have hpt2 : ∑ x ∈ Finset.range 1009, ((-1:ℝ)^(1009-x) * (Nat.choose 1009 x : ℝ)) * P.eval (2*(x:ℝ)+1) + P.eval 2019 = 0 := by
    have h := hpt
    simp only [Pi.zero_apply, zsmul_eq_mul, hQeval, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, one_mul, Nat.cast_ofNat] at h
    norm_num at h
    linarith [h]
  have hc : ∀ x ∈ Finset.range 1009, P.eval (2*(x:ℝ)+1) = (Nat.fib (2*x+1) : ℝ) := by
    intro x hx
    have hx' := Finset.mem_range.mp hx
    rw [hp x (by omega)]
    have := hFibF (2*x+1) (by omega)
    rw [this]
    simp
  have hsumR : ∑ x ∈ Finset.range 1009, ((-1:ℝ)^(1009-x) * (Nat.choose 1009 x : ℝ)) * P.eval (2*(x:ℝ)+1)
      = ∑ x ∈ Finset.range 1009, ((-1:ℝ)^(1009-x) * (Nat.choose 1009 x : ℝ)) * (Nat.fib (2*x+1) : ℝ) :=
    Finset.sum_congr rfl (fun x hx => by rw [hc x hx])
  have hint : ∑ k ∈ Finset.range 1009, (-1:ℤ)^(1009-k) * ((Nat.choose 1009 k : ℕ) : ℤ) * (Nat.fib (2*k+1) : ℤ)
      = (Nat.fib 1010 : ℤ) - (Nat.fib 2019 : ℤ) := by
    have hch : ∀ k ∈ Finset.range 1009, ((Nat.choose 1009 k : ℕ) : ℤ) = ((Nat.factorial 1009 / (Nat.factorial k * Nat.factorial (1009-k)) : ℕ) : ℤ) := by
      intro k hk
      rw [Nat.choose_eq_factorial_div_factorial (by have := Finset.mem_range.mp hk; omega)]
    rw [Finset.sum_congr rfl (fun k hk => by rw [hch k hk])]
    decide +kernel
  have hR : ∑ x ∈ Finset.range 1009, ((-1:ℝ)^(1009-x) * (Nat.choose 1009 x : ℝ)) * (Nat.fib (2*x+1) : ℝ)
      = (Nat.fib 1010 : ℝ) - (Nat.fib 2019 : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) hint
    push_cast at this
    linarith [this]
  have key : P.eval 2019 = (Nat.fib 2019 : ℝ) - (Nat.fib 1010 : ℝ) := by
    linarith [hpt2, hsumR, hR]
  -- Fibonacci facts for uniqueness
  have hmono : Monotone Nat.fib := Nat.fib_mono
  have hL : ∀ a b, 1 ≤ a → a < b → 3 ≤ b → Nat.fib a < Nat.fib b := by
    intro a b ha hab hb
    rcases Nat.lt_or_ge a 2 with h | h
    · have ha1 : a = 1 := by omega
      subst ha1
      have h3 : Nat.fib 3 = 2 := by decide
      have := hmono hb
      rw [h3] at this
      rw [Nat.fib_one]
      omega
    · obtain ⟨c, rfl⟩ : ∃ c, a = c + 2 := ⟨a - 2, by omega⟩
      obtain ⟨d, rfl⟩ : ∃ d, b = d + 2 := ⟨b - 2, by omega⟩
      exact Nat.fib_add_two_strictMono (by omega : c < d)
  have hpos : ∀ n, 1 ≤ n → 1 ≤ Nat.fib n := fun n hn => Nat.fib_pos.2 (by omega)
  have hA : Nat.fib 1010 < Nat.fib 2017 := hL 1010 2017 (by norm_num) (by norm_num) (by norm_num)
  have hB : Nat.fib 1010 < Nat.fib 2019 := hL 1010 2019 (by norm_num) (by norm_num) (by norm_num)
  have h19 : Nat.fib 2019 = Nat.fib 2017 + Nat.fib 2018 := by
    rw [show (2019:ℕ) = 2017 + 2 from rfl, Nat.fib_add_two]
  have p1010 := hpos 1010 (by norm_num)
  have uniq : ∀ j k : ℕ, 1 ≤ j → 1 ≤ k →
      (Nat.fib 2019 : ℤ) - (Nat.fib 1010 : ℤ) = (Nat.fib j : ℤ) - (Nat.fib k : ℤ) → j = 2019 ∧ k = 1010 := by
    intro j k hj hk h
    have hN : Nat.fib j + Nat.fib 1010 = Nat.fib 2019 + Nat.fib k := by omega
    rcases le_or_gt j k with hjk | hjk
    · have := hmono hjk
      omega
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have hk1 : Nat.fib k ≤ Nat.fib (m+1) := hmono (by omega)
      have hfm : Nat.fib (m+2) = Nat.fib m + Nat.fib (m+1) := Nat.fib_add_two
      have pk := hpos k hk
      have hm : m < 2019 := by
        by_contra hc
        have := hmono (show 2019 ≤ m by omega)
        omega
      have hj2 : 2017 ≤ m := by
        by_contra hc
        have := hmono (show m + 2 ≤ 2018 by omega)
        omega
      obtain rfl | rfl : m = 2017 ∨ m = 2018 := by omega
      · have e1 : Nat.fib (2017+2) = Nat.fib 2019 := congrArg Nat.fib (by norm_num)
        rw [e1] at hN
        have hk' : k = 1010 := by
          rcases lt_trichotomy k 1010 with h1 | h1 | h1
          · have := hL k 1010 hk h1 (by norm_num)
            omega
          · exact h1
          · have := hL 1010 k (by norm_num) h1 (by omega)
            omega
        exact ⟨by norm_num, hk'⟩
      · have e1 : Nat.fib (2018+2) = Nat.fib 2020 := congrArg Nat.fib (by norm_num)
        rw [e1] at hN
        have h2020 : Nat.fib 2020 = Nat.fib 2018 + Nat.fib 2019 := by
          rw [show (2020:ℕ) = 2018 + 2 from rfl, Nat.fib_add_two]
        exfalso
        have h1 : 2019 ≤ k := by
          by_contra hc
          have := hmono (show k ≤ 2018 by omega)
          omega
        have h2 : k ≤ 2018 := by
          by_contra hc
          have := hmono (show 2019 ≤ k by omega)
          omega
        omega
  intro j k
  constructor
  · rintro ⟨h, hj, hk⟩
    rw [key] at h
    have h' : (Nat.fib 2019 : ℤ) - (Nat.fib 1010 : ℤ) = (F j) - (F k) := by
      have : ((((Nat.fib 2019 : ℤ) - (Nat.fib 1010 : ℤ) : ℤ)) : ℝ) = (((F j) - (F k) : ℤ) : ℝ) := by
        push_cast
        linarith [h]
      exact_mod_cast this
    rw [hFibF j hj, hFibF k hk] at h'
    obtain ⟨rfl, rfl⟩ := uniq j k hj hk h'
    rfl
  · intro h
    simp only [putnam_2019_b5_solution, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, by norm_num, by norm_num⟩
    rw [key, hFibF 2019 (by norm_num), hFibF 1010 (by norm_num)]
    push_cast
    ring
