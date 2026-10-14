import Mathlib

open Set Nat Function

theorem putnam_2007_b5
(k : ℕ) (kpos : k > 0) :
(∃ P : Finset.range k → Polynomial ℝ, ∀ n : ℤ, ⌊(n : ℝ) / k⌋ ^ k = ∑ i : Finset.range k, (P i).eval (n : ℝ) * ⌊(n : ℝ) / k⌋ ^ (i : ℕ)) := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℕ → Polynomial (Polynomial ℝ), g = fun (j : ℕ) =>
      Polynomial.C (Polynomial.X : Polynomial ℝ) - Polynomial.C (k : Polynomial ℝ) * Polynomial.X
        - Polynomial.C (j : Polynomial ℝ) :=
    ⟨fun (j : ℕ) => Polynomial.C (Polynomial.X : Polynomial ℝ) - Polynomial.C (k : Polynomial ℝ) * Polynomial.X
        - Polynomial.C (j : Polynomial ℝ), rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Polynomial (Polynomial ℝ), F = ∏ j ∈ Finset.range k, g j :=
    ⟨∏ j ∈ Finset.range k, g j, rfl⟩
  have hg1 : ∀ j, (g j).natDegree ≤ 1 := by
    intro j; rw [hg]; dsimp only; compute_degree!
  have hg2 : ∀ j, (g j).coeff 1 = -(k : Polynomial ℝ) := by
    intro j; rw [hg]; simp
  have hmul : ∀ (p q : Polynomial (Polynomial ℝ)) (d : ℕ), p.natDegree ≤ 1 → q.natDegree ≤ d →
      (p * q).coeff (1 + d) = p.coeff 1 * q.coeff d := by
    intro p q d hp hq
    rw [Polynomial.coeff_mul, Finset.sum_eq_single (1, d)]
    · intro x hx hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      obtain ⟨a, b⟩ := x

      rcases Nat.lt_or_ge 1 a with h | h
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h), zero_mul]
      · rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < b), mul_zero]
        · have hb : b = d := by omega
          subst hb
          exact absurd rfl hne
    · intro h
      exact (h (by simp)).elim
  have key : ∀ s : Finset ℕ, (∏ j ∈ s, g j).natDegree ≤ s.card ∧
      (∏ j ∈ s, g j).coeff s.card = (-(k : Polynomial ℝ)) ^ s.card := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      obtain ⟨h1, h2⟩ := ih
      constructor
      · calc _ ≤ (g a).natDegree + (∏ j ∈ s, g j).natDegree := Polynomial.natDegree_mul_le
          _ ≤ 1 + s.card := _root_.add_le_add (hg1 a) h1
          _ = _ := by ring
      · rw [show s.card + 1 = 1 + s.card by ring, hmul _ _ _ (hg1 a) h1, h2, hg2]
        ring
  have hFdeg : F.natDegree ≤ k ∧ F.coeff k = (-(k : Polynomial ℝ)) ^ k := by
    have := key (Finset.range k)
    rw [Finset.card_range] at this
    rw [hF]; exact this
  have hev : ∀ a b : ℝ, (F.map (Polynomial.evalRingHom a)).eval b
      = ∏ j ∈ Finset.range k, (a - k * b - j) := by
    intro a b
    rw [hF]
    simp [hg, Polynomial.map_prod, Polynomial.eval_prod]
  have hkpos : (0:ℝ) < k := by exact_mod_cast kpos
  have hc0 : (-(k:ℝ)) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 hkpos.ne')
  refine ⟨fun i => Polynomial.C (-(1 / (-(k:ℝ)) ^ k)) * F.coeff (i : ℕ), ?_⟩
  intro n
  have h1 : ((⌊(n:ℝ)/k⌋ : ℤ) : ℝ) ≤ n / k := Int.floor_le _
  have h2 : (n:ℝ)/k < ((⌊(n:ℝ)/k⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  generalize ⌊(n:ℝ)/k⌋ = m at h1 h2 ⊢
  have h1' : (k:ℝ) * m ≤ n := by rw [le_div_iff₀ hkpos] at h1; linarith
  have h2' : (n:ℝ) < k * m + k := by rw [div_lt_iff₀ hkpos] at h2; linarith
  have h1z : (k:ℤ) * m ≤ n := by exact_mod_cast h1'
  have h2z : (n:ℤ) < k * m + k := by exact_mod_cast h2'
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j:ℤ) = n - k * m := ⟨(n - k * m).toNat, by omega⟩
  have hjk : j < k := by
    have : (j:ℤ) < k := by linarith
    exact_mod_cast this
  have hjR : (j:ℝ) = (n:ℝ) - k * m := by exact_mod_cast hj
  have hz : (F.map (Polynomial.evalRingHom (n:ℝ))).eval (m:ℝ) = 0 := by
    rw [hev]
    apply Finset.prod_eq_zero (i := j) (Finset.mem_range.2 hjk)
    linarith
  have hsum := Polynomial.eval_eq_sum_range' (p := F.map (Polynomial.evalRingHom (n:ℝ)))
    (n := k + 1) (by have := Polynomial.natDegree_map_le (p := F) (f := Polynomial.evalRingHom (n:ℝ)); omega) (m:ℝ)
  rw [hz] at hsum
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] at hsum
  rw [Finset.sum_range_succ, hFdeg.2] at hsum
  have hck : (Polynomial.eval (n:ℝ) ((-(k : Polynomial ℝ)) ^ k)) = (-(k:ℝ))^k := by
    simp
  rw [hck] at hsum
  have hs : ∑ i ∈ Finset.range k, (F.coeff i).eval (n:ℝ) * (m:ℝ) ^ i = -((-(k:ℝ))^k) * (m:ℝ)^k := by
    linarith
  rw [Finset.sum_coe_sort (Finset.range k)
    (fun i : ℕ => (Polynomial.C (-(1 / (-(k:ℝ)) ^ k)) * F.coeff i).eval (n:ℝ) * (m:ℝ) ^ i)]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (∑ x ∈ Finset.range k, -(1 / (-(k:ℝ)) ^ k) * (F.coeff x).eval (n:ℝ) * (m:ℝ) ^ x) = -(1 / (-(k:ℝ)) ^ k) * ∑ x ∈ Finset.range k, (F.coeff x).eval (n:ℝ) * (m:ℝ) ^ x from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by ring), hs]
  field_simp
