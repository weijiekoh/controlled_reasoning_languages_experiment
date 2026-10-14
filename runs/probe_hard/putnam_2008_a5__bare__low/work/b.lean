import Mathlib
open Polynomial
example (n : ℕ)
(nge3 : n ≥ 3)
(f g : Polynomial ℝ)
(hfg : ∃ O z : ℂ, z ≠ 0 ∧ ∀ k : ℕ, k ∈ Set.Icc 1 n → (f.eval (k : ℝ)) + Complex.I * (g.eval (k : ℝ)) = O + z * Complex.exp (Complex.I * 2 * Real.pi * k / n))
: (f.natDegree ≥ n - 1 ∨ g.natDegree ≥ n - 1) := by
  by_contra h
  push_neg at h
  obtain ⟨O, z, hz, H⟩ := hfg
  obtain ⟨P, hP⟩ : ∃ P : ℂ[X], P = f.map Complex.ofRealHom + C Complex.I * g.map Complex.ofRealHom := ⟨_, rfl⟩
  have hdeg : P.natDegree < n - 1 := by
    have h1 : (f.map Complex.ofRealHom).natDegree ≤ f.natDegree := natDegree_map_le
    have h2 : (C Complex.I * g.map Complex.ofRealHom).natDegree ≤ g.natDegree :=
      (natDegree_C_mul_le _ _).trans natDegree_map_le
    have h3 : P.natDegree ≤ _ := hP ▸ natDegree_add_le (f.map Complex.ofRealHom) (C Complex.I * g.map Complex.ofRealHom)
    omega
  have h0 := congrFun (fwdDiff_iter_eq_zero_of_degree_lt hdeg) 1
  rw [fwdDiff_iter_eq_sum_shift] at h0
  set ω : ℂ := Complex.exp (Complex.I * 2 * Real.pi / n) with hω
  have hval : ∀ k ∈ Finset.range (n - 1 + 1),
      ((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) • eval (1 + k • (1:ℂ)) P
      = ((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) * O + (z * ω) * (((-1 : ℂ) ^ (n - 1 - k) * ((n - 1).choose k : ℂ)) * ω ^ k) := by
    intro k hk
    have hk' : k + 1 ∈ Set.Icc 1 n := by
      simp at hk; constructor <;> omega
    have := H (k+1) hk'
    have e : eval (1 + k • (1:ℂ)) P = f.eval ((k+1:ℕ):ℝ) + Complex.I * g.eval ((k+1:ℕ):ℝ) := by
      simp [hP, eval_map, ← Polynomial.eval₂_at_apply]
      trace_state
      sorry
    have e2 : Complex.exp (Complex.I * 2 * Real.pi * ((k+1:ℕ):ℂ) / n) = ω ^ (k+1) := by
      rw [hω, ← Complex.exp_nat_mul]; congr 1; ring
    sorry
  sorry
