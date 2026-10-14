import Mathlib

open Nat Set

/--
Let $H$ be an $n \times n$ matrix all of whose entries are $\pm 1$ and whose rows are mutually orthogonal. Suppose $H$ has an $a \times b$ submatrix whose entries are all $1$. Show that $ab \leq n$.
-/
theorem putnam_2005_a4
(n : ℕ)
(H : Matrix (Fin n) (Fin n) ℝ)
(a b : ℕ)
(S : Matrix (Fin a) (Fin b) ℝ)
(npos : n ≥ 1)
(Hentries : ∀ i j : Fin n, H i j = 1 ∨ H i j = -1)
(Hortho : H.HasOrthogonalRows)
(hab : 1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n)
(Ssub : ∃ (rri : Fin a → Fin n) (cri : Fin b → Fin n), rri.Injective ∧ cri.Injective ∧ S = H.submatrix rri cri)
(Sentries : ∀ (i : Fin a) (j : Fin b), S i j = 1)
: a * b ≤ n := by
  obtain ⟨rri, cri, hr, hc, hS⟩ := Ssub
  have h1 : H * H.transpose = (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases h : i = i'
    · subst h
      have hk : ∀ k, H i k * H i k = 1 := fun k => by
        rcases Hentries i k with h | h <;> rw [h] <;> norm_num
      simp [hk]
    · rw [if_neg h, mul_zero]
      have := Hortho h
      simpa [dotProduct, mul_comm] using this
  have hn : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2 : H.transpose * H = (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hinv : H * ((n:ℝ)⁻¹ • H.transpose) = 1 := by
      rw [Matrix.mul_smul, h1, smul_smul, inv_mul_cancel₀ hn, one_smul]
    have := (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℝ rfl).mp hinv
    rw [Matrix.smul_mul] at this
    calc H.transpose * H = (n:ℝ) • ((n:ℝ)⁻¹ • (H.transpose * H)) := by
          rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = (n:ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [this]
  have hcol : ∀ j k : Fin n, ∑ i, H i j * H i k = if j = k then (n:ℝ) else 0 := by
    intro j k
    have := congrFun (congrFun h2 j) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at this
    rw [this]
    by_cases h : j = k <;> simp [h]
  set s : Fin n → ℝ := fun i => ∑ j : Fin b, H i (cri j) with hsdef
  have key1 : ∑ i, s i * s i = (n:ℝ) * b := by
    calc ∑ i, s i * s i = ∑ i, ∑ j, ∑ l, H i (cri j) * H i (cri l) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [hsdef, Finset.sum_mul_sum]
      _ = ∑ j, ∑ l, ∑ i, H i (cri j) * H i (cri l) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ j, ∑ l : Fin b, if j = l then (n:ℝ) else 0 := by
          refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
          rw [hcol]; simp only [hc.eq_iff]
      _ = (n:ℝ) * b := by
          simp [Finset.sum_ite_eq]; ring
  have hSij : ∀ i j, H (rri i) (cri j) = S i j := by
    intro i j
    rw [hS]
    rfl
  have key2 : ∀ i : Fin a, s (rri i) = b := by
    intro i
    simp only [hsdef, hSij, Sentries]
    simp
  have key3 : ∑ i : Fin a, s (rri i) * s (rri i) ≤ ∑ i, s i * s i := by
    have : ∑ i : Fin a, s (rri i) * s (rri i) = ∑ x ∈ (Finset.univ.image rri), s x * s x := by
      rw [Finset.sum_image]
      intro x _ y _ h
      exact hr h
    rw [this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => mul_self_nonneg _)
  simp only [key2] at key3
  rw [key1] at key3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at key3
  have hb : (0:ℝ) < b := by
    have : (1:ℝ) ≤ b := by exact_mod_cast hab.2.2.1
    linarith
  have key4 : ((a * b : ℕ) : ℝ) * b ≤ (n:ℝ) * b := by
    push_cast
    linarith
  have key5 : ((a * b : ℕ) : ℝ) ≤ n := le_of_mul_le_mul_right key4 hb
  exact_mod_cast key5
