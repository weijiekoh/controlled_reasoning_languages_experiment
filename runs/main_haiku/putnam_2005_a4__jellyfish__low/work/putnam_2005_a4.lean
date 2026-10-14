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
  classical
  obtain ⟨rri, cri, hri, hci, hS⟩ := Ssub
  have hn : (n:ℝ) ≠ 0 := by positivity
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast hab.2.2.1
  have hH : H * H.transpose = (n:ℝ) • 1 := by
    ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : i = k
    · subst h
      have hsq : ∀ j, H i j * H i j = 1 := fun j => by
        rcases Hentries i j with h | h <;> rw [h] <;> norm_num
      simp [hsq]
    · have := Hortho h
      simp only [dotProduct] at this
      simp [h, this]
  have hcol : ∀ c c' : Fin n, ∑ r, H r c * H r c' = if c = c' then (n:ℝ) else 0 := by
    intro c c'
    have h1 : ((n:ℝ)⁻¹ • H) * H.transpose = 1 := by
      rw [Matrix.smul_mul, hH, smul_smul, inv_mul_cancel₀ hn, one_smul]
    have h2 := (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℝ rfl).mp h1
    have hK : H.transpose * H = (n:ℝ) • 1 := by
      calc H.transpose * H = (n:ℝ) • (H.transpose * ((n:ℝ)⁻¹ • H)) := by
            rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hn, one_smul]
        _ = (n:ℝ) • 1 := by rw [h2]
    have := congrFun (congrFun hK c) c'
    by_cases h : c = c'
    · subst h
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    · simpa [Matrix.mul_apply, Matrix.one_apply, h] using this
  set w : Fin n → ℝ := fun r => ∑ j : Fin b, H r (cri j) with hw_def
  have hpair : ∀ j j' : Fin b, ∑ r, H r (cri j) * H r (cri j') = if j = j' then (n:ℝ) else 0 := by
    intro j j'
    rw [hcol]; exact if_congr hci.eq_iff rfl rfl
  have key1 : ∑ r, (w r)^2 = (n:ℝ) * b := by
    have hsq : ∀ r, (w r)^2 = ∑ j, ∑ j', H r (cri j) * H r (cri j') := fun r => by
      simp only [hw_def, sq, Finset.sum_mul_sum]
    simp only [hsq]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
    simp only [hpair, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [Finset.sum_const, Finset.card_univ, mul_comm]
  have hH1 : ∀ i j, H (rri i) (cri j) = 1 := fun i j => by
    have := Sentries i j
    rw [hS] at this
    simpa [Matrix.submatrix_apply] using this
  have hwi : ∀ i, w (rri i) = (b:ℝ) := fun i => by
    simp [hw_def, hH1]
  have key2 : ∑ i, (w (rri i))^2 = (a:ℝ) * (b:ℝ)^2 := by
    simp only [hwi]
    simp [Finset.sum_const, Finset.card_univ]
  have key3 : ∑ i, (w (rri i))^2 ≤ ∑ r, (w r)^2 := by
    rw [← Finset.sum_image (f := fun r => (w r)^2) (fun x _ y _ hxy => hri hxy)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun r _ _ => sq_nonneg _)
  have hfin : (a:ℝ) * b * b ≤ (n:ℝ) * b := by
    nlinarith [key1, key2, key3]
  have hbpos : (0:ℝ) < b := by linarith
  have := le_of_mul_le_mul_right hfin hbpos
  exact_mod_cast this
