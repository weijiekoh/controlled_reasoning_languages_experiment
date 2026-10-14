import Mathlib

open Topology Filter Set Matrix

noncomputable abbrev putnam_2019_b5_solution : ℕ × ℕ := ⟨2019, 1010⟩

lemma fd_sum (N : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ N) :
    ∑ k ∈ Finset.range (N+2), ((-1:ℝ)^(N+1-k) * ((N+1).choose k : ℝ)) * P.eval (2*(k:ℝ)+1) = 0 := by
  set R := P.comp (2*Polynomial.X+1) with hRdef
  have h1 : (2*Polynomial.X+1 : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
  have hdeg : R.natDegree < N+1 :=
    lt_of_le_of_lt (le_trans Polynomial.natDegree_comp_le (by simpa using Nat.mul_le_mul hP h1)) (by omega)
  have hev : ∀ k : ℕ, P.eval (2*(k:ℝ)+1) = R.eval (k:ℝ) := by
    intro k; simp [hRdef, Polynomial.eval_comp]
  simp only [hev]
  have key : ∀ i ∈ Finset.range (N+1), ∑ k ∈ Finset.range (N+2),
      ((-1:ℝ)^(N+1-k) * ((N+1).choose k : ℝ)) * (k:ℝ)^i = 0 := by
    intro i hi
    have hi' : i < N+1 := Finset.mem_range.mp hi
    have h0 := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) (j := i) (n := N+1) (by omega)) 0
    rw [fwdDiff_iter_eq_sum_shift] at h0
    simp only [Pi.zero_apply, nsmul_eq_mul, zero_add, mul_one] at h0
    simpa using h0
  have expand : ∀ k : ℕ, R.eval (k:ℝ) = ∑ i ∈ Finset.range (N+1), R.coeff i * (k:ℝ)^i :=
    fun k => Polynomial.eval_eq_sum_range' hdeg _
  simp only [expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  have := key i hi
  calc ∑ k ∈ Finset.range (N+2), ((-1:ℝ)^(N+1-k) * ((N+1).choose k : ℝ)) * (R.coeff i * (k:ℝ)^i)
      = R.coeff i * ∑ k ∈ Finset.range (N+2), ((-1:ℝ)^(N+1-k) * ((N+1).choose k : ℝ)) * (k:ℝ)^i := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = 0 := by rw [this, mul_zero]

lemma geom_sum (N : ℕ) (x : ℝ) :
    ∑ k ∈ Finset.range (N+1), ((-1:ℝ)^(N-k) * ((N+1).choose k : ℝ)) * x^k = x^(N+1) - (x-1)^(N+1) := by
  have h2 : (x-1)^(N+1) = ∑ m ∈ Finset.range (N+1), x^m * (-1:ℝ)^(N+1-m) * ((N+1).choose m : ℝ) + x^(N+1) := by
    rw [sub_eq_add_neg, add_pow, Finset.sum_range_succ]; simp
  have e : ∀ k ∈ Finset.range (N+1), ((-1:ℝ)^(N-k) * ((N+1).choose k : ℝ)) * x^k
      = -(x^k * (-1:ℝ)^(N+1-k) * ((N+1).choose k : ℝ)) := by
    intro k hk
    have hk' : k < N+1 := Finset.mem_range.mp hk
    have : N+1-k = (N-k)+1 := by omega
    rw [this, pow_succ]; ring
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
  linarith

lemma binet_sum (N : ℕ) :
    ∑ k ∈ Finset.range (N+1), ((-1:ℝ)^(N-k) * ((N+1).choose k : ℝ)) * ((Nat.fib (2*k+1) : ℕ) : ℝ)
      = ((Nat.fib (2*N+3) : ℕ) : ℝ) - ((Nat.fib (N+2) : ℕ) : ℝ) := by
  have hc := Real.coe_fib_eq
  have hφ := Real.goldenRatio_sq
  have hψ := Real.goldenConj_sq
  generalize Real.goldenRatio = φ at *
  generalize Real.goldenConj = ψ at *
  have hφ' : φ^2 - 1 = φ := by linarith
  have hψ' : ψ^2 - 1 = ψ := by linarith
  have hb : ∀ k : ℕ, ((Nat.fib (2*k+1) : ℕ) : ℝ) = (φ^(2*k+1) - ψ^(2*k+1)) / Real.sqrt 5 :=
    fun k => hc _
  have hs : ∀ k ∈ Finset.range (N+1), ((-1:ℝ)^(N-k) * ((N+1).choose k : ℝ)) * ((Nat.fib (2*k+1) : ℕ) : ℝ)
      = (φ * (((-1:ℝ)^(N-k) * ((N+1).choose k : ℝ)) * (φ^2)^k)
         - ψ * (((-1:ℝ)^(N-k) * ((N+1).choose k : ℝ)) * (ψ^2)^k)) / Real.sqrt 5 := by
    intro k _
    rw [hb k]; ring
  rw [Finset.sum_congr rfl hs, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [geom_sum N (φ^2), geom_sum N (ψ^2), hφ', hψ', hc (2*N+3), hc (N+2)]
  ring

lemma fib_uniq (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    (h : ((Nat.fib j : ℕ) : ℤ) - ((Nat.fib k : ℕ) : ℤ) = ((Nat.fib 2019 : ℕ) : ℤ) - ((Nat.fib 1010 : ℕ) : ℤ)) :
    j = 2019 ∧ k = 1010 := by
  have mono : ∀ a b : ℕ, a ≤ b → ((Nat.fib a : ℕ) : ℤ) ≤ (Nat.fib b : ℕ) := fun a b hab => by
    exact_mod_cast Nat.fib_mono hab
  have strict : ∀ a b : ℕ, 2 ≤ a → a < b → ((Nat.fib a : ℕ) : ℤ) < (Nat.fib b : ℕ) := fun a b ha hab => by
    have h1 := Nat.fib_lt_fib_succ ha
    have h2 := mono (a+1) b (by omega)
    have h1' : ((Nat.fib a : ℕ) : ℤ) < (Nat.fib (a+1) : ℕ) := by exact_mod_cast h1
    linarith
  have pos : ∀ a : ℕ, 1 ≤ a → (1:ℤ) ≤ (Nat.fib a : ℕ) := fun a ha => by
    have := Nat.fib_pos.mpr (by omega : 0 < a)
    exact_mod_cast this
  have rec2017 := @Nat.fib_add_two 2017
  simp only [Nat.reduceAdd] at rec2017
  have rec2017Z : ((Nat.fib 2019 : ℕ) : ℤ) = (Nat.fib 2018 : ℕ) + (Nat.fib 2017 : ℕ) := by
    rw [rec2017]; push_cast; ring
  have p1010 := pos 1010 (by norm_num)
  have s1010_2019 := strict 1010 2019 (by norm_num) (by norm_num)
  have s1010_2017 := strict 1010 2017 (by norm_num) (by norm_num)
  have m2017 := mono 1010 2017 (by norm_num)
  rcases lt_or_ge k j with hkj | hkj
  · by_cases hj2 : j ≤ 2018
    · have := mono j 2018 hj2
      have := pos k hk
      linarith
    · have hj2' : 2019 ≤ j := by omega
      rcases (show j = 2019 ∨ j ≥ 2020 by omega) with hj4 | hj3
      · subst hj4
        rcases lt_trichotomy k 1010 with hk1 | hk1 | hk1
        · have := mono k 1009 (by omega)
          have := strict 1009 1010 (by norm_num) (by norm_num)
          linarith
        · exact ⟨rfl, hk1⟩
        · have := mono 1011 k (by omega)
          have := strict 1010 1011 (by norm_num) (by norm_num)
          linarith
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
        have hrec := Nat.fib_add_two (n := m)
        have hrecZ : ((Nat.fib (m+2) : ℕ) : ℤ) = (Nat.fib m : ℕ) + (Nat.fib (m+1) : ℕ) := by
          exact_mod_cast hrec
        have hk' : k = m + 1 := by
          by_contra hne
          have hkm : k ≤ m := by omega
          have := mono k m hkm
          have := mono 2019 (m+1) (by omega)
          linarith
        subst hk'
        rcases (show m = 2018 ∨ m ≥ 2019 by omega) with hm | hm
        · exfalso
          have e1 : ((Nat.fib (m+1) : ℕ) : ℤ) = (Nat.fib 2019 : ℕ) := by rw [hm]
          have e2 : ((Nat.fib m : ℕ) : ℤ) = (Nat.fib 2018 : ℕ) := by rw [hm]
          linarith
        · have := mono 2019 m (by omega)
          linarith
  · have := mono j k hkj
    have := strict 1010 2019 (by norm_num) (by norm_num)
    linarith

lemma P_val (N : ℕ) (P : Polynomial ℝ) (hP : P.natDegree ≤ N)
    (hF : ∀ k, k ≤ N → P.eval (2*(k:ℝ)+1) = ((Nat.fib (2*k+1) : ℕ) : ℝ)) :
    P.eval (2*(N:ℝ)+3) = ((Nat.fib (2*N+3) : ℕ) : ℝ) - ((Nat.fib (N+2) : ℕ) : ℝ) := by
  have h := fd_sum N P hP
  rw [Finset.sum_range_succ] at h
  have hlast : (2*(((N+1 : ℕ)) : ℝ)+1) = 2*(N:ℝ)+3 := by push_cast; ring
  have hsum : ∑ k ∈ Finset.range (N+1), ((-1:ℝ)^(N+1-k) * ((N+1).choose k : ℝ)) * P.eval (2*(k:ℝ)+1)
      = -(((Nat.fib (2*N+3) : ℕ) : ℝ) - ((Nat.fib (N+2) : ℕ) : ℝ)) := by
    rw [← binet_sum N, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < N+1 := Finset.mem_range.mp hk
    rw [hF k (by omega)]
    have : N+1-k = (N-k)+1 := by omega
    rw [this, pow_succ]; ring
  simp only [Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, hlast] at h
  linarith

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
  have hFib2 : ∀ n : ℕ, F (n+1) = (Nat.fib (n+1) : ℤ) ∧ F (n+2) = (Nat.fib (n+2) : ℤ) := by
    intro n
    induction n with
    | zero => simp [F12.1, F12.2]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 := hF (n+1) (by omega)
      have h2 := Nat.fib_add_two (n := n+1)
      rw [show n + 1 + 2 = n + 3 by ring, show n + 1 + 1 = n + 2 by ring] at h1
      rw [show n + 1 + 2 = n + 3 by ring, h2, h1, ih.1, ih.2]
      push_cast; ring_nf
  have hFib : ∀ n, 1 ≤ n → F n = (Nat.fib n : ℤ) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
    exact (hFib2 m).1
  have hdeg : P.natDegree ≤ 1008 := Polynomial.natDegree_le_of_degree_le (le_of_eq Pdeg)
  have hPv := P_val 1008 P hdeg (fun k hk => by rw [hp k hk, hFib (2*k+1) (by omega)]; norm_cast)
  rw [show (2*(1008:ℕ):ℝ)+3 = 2019 by norm_num, show 2*1008+3 = 2019 from rfl,
    show 1008+2 = 1010 from rfl] at hPv
  intro j k
  constructor
  · rintro ⟨h, hj, hk⟩
    rw [hPv, hFib j hj, hFib k hk] at h
    have hz : ((Nat.fib j : ℕ) : ℤ) - ((Nat.fib k : ℕ) : ℤ) = ((Nat.fib 2019 : ℕ) : ℤ) - ((Nat.fib 1010 : ℕ) : ℤ) := by
      have h3 : (((((Nat.fib j : ℕ) : ℤ) - ((Nat.fib k : ℕ) : ℤ)) : ℤ) : ℝ)
          = ((((Nat.fib 2019 : ℕ) : ℤ) - ((Nat.fib 1010 : ℕ) : ℤ) : ℤ) : ℝ) := by
        push_cast at h ⊢; linarith
      exact Int.cast_injective h3
    obtain ⟨h1, h2⟩ := fib_uniq j k hj hk hz
    subst h1; subst h2
    rfl
  · intro h
    have h' : j = 2019 ∧ k = 1010 := by
      simp [putnam_2019_b5_solution] at h
      exact h
    obtain ⟨rfl, rfl⟩ := h'
    refine ⟨?_, by norm_num, by norm_num⟩
    rw [hPv, hFib 2019 (by norm_num), hFib 1010 (by norm_num)]
    push_cast; ring
