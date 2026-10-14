
open Real Set Nat

noncomputable abbrev putnam_2016_b4_solution : ℕ → ℝ := (fun n : ℕ => (2 * n)! / (4 ^ n * (n)!))
/--
Let $A$ be a $2n \times 2n$ matrix, with entries chosen independently at random. Every entry is chosen to be $0$ or $1$, each with probability $1/2$. Find the expected value of $\det(A-A^t)$ (as a function of $n$), where $A^t$ is the transpose of $A$.
-/
theorem putnam_2016_b4
  (n : ℕ) (npos : n ≥ 1)
  (mats01 : Set (Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
  (hmats01 : mats01 = {A | ∀ i j : Fin (2 * n), A i j = 0 ∨ A i j = 1}) :
  (∑' A : mats01, (A.1 - (Matrix.transpose A)).det) / mats01.ncard = putnam_2016_b4_solution n :=
by
  have hm : ∀ M, M ∈ mats01 ↔ ∀ i j : Fin (2 * n), M i j = 0 ∨ M i j = 1 := by
    intro M; rw [hmats01]; rfl
  let e : (Fin (2*n) × Fin (2*n) → Bool) ≃ mats01 :=
    { toFun := fun f => ⟨Mf f, by
        rw [hm]; intro i j; simp only [Mf, vv]; split_ifs <;> simp⟩
      invFun := fun A p => decide (A.1 p.1 p.2 = 1)
      left_inv := by
        intro f; funext p; simp [Mf, vv]
      right_inv := by
        intro A; apply Subtype.ext; funext i j
        have := (hm A.1).mp A.2
        rcases this i j with h | h <;> simp [Mf, vv, h] }
  have hcard : (mats01.ncard : ℝ) = 2 ^ ((2*n) * (2*n)) := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr e]
    simp
  rw [← Equiv.tsum_eq e, tsum_fintype]
  have hs := sumdet n npos
  have hc := count_inv n npos
  have hc' : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card : ℝ)
      * (2 ^ n * (n.factorial : ℝ)) = ((2 * n).factorial : ℝ) := by exact_mod_cast hc
  have : ∑ f, ((e f).1 - (e f).1.transpose).det = ∑ f : Fin (2*n) × Fin (2*n) → Bool, (Mf f - (Mf f).transpose).det := rfl
  rw [this, hs, hcard]
  simp only [putnam_2016_b4_solution]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity), ← hc']
  have : (4:ℝ)^n = 2^n * 2^n := by rw [← mul_pow]; norm_num
  rw [this, one_div, inv_pow]
  field_simp
