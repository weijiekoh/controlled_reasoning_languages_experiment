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
  obtain ⟨rri, cri, hri, hci, hS⟩ := Ssub
  obtain ⟨ha1, han, hb1, hbn⟩ := hab
  have hdiag : ∀ i : Fin n, H i ⬝ᵥ H i = (n:ℝ) := by
    intro i
    have : ∀ k, H i k * H i k = 1 := by
      intro k
      rcases Hentries i k with h | h <;> simp [h]
    simp only [dotProduct, this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hrow : ∀ i i' : Fin a, H (rri i) ⬝ᵥ H (rri i') = if i = i' then (n:ℝ) else 0 := by
    intro i i'
    by_cases h : i = i'
    · subst h; simp [hdiag]
    · rw [if_neg h]
      exact Hortho (fun e => h (hri e))
  have hrow_sum : ∀ i i' : Fin a, ∑ k, H (rri i) k * H (rri i') k = if i = i' then (n:ℝ) else 0 :=
    fun i i' => hrow i i'
  have hcell : ∀ i j, H (rri i) (cri j) = 1 := by
    intro i j
    have h1 := Sentries i j
    rw [hS] at h1
    simpa [Matrix.submatrix] using h1
  set x : Fin n → ℝ := fun k => ∑ j : Fin b, if cri j = k then (1:ℝ) else 0 with hx
  set s : Fin n → ℝ := fun k => ∑ i : Fin a, H (rri i) k with hs
  have F1 : ∀ i : Fin a, ∑ k, H (rri i) k * x k = (b:ℝ) := by
    intro i
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ j : Fin b, ∑ k, H (rri i) k * (if cri j = k then (1:ℝ) else 0) = 1 := by
      intro j
      simp [mul_ite, hcell]
    simp [hcell]
  have hxv : ∀ k, x k * x k = x k := by
    intro k
    by_cases h : ∃ j, cri j = k
    · obtain ⟨j, hj⟩ := h
      have : x k = 1 := by
        simp only [hx]
        rw [Finset.sum_eq_single j]
        · simp [hj]
        · intro j' _ hne
          rw [if_neg]
          intro e
          exact hne (hci (e.trans hj.symm))
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [this]; norm_num
    · push Not at h
      have : x k = 0 := by
        simp only [hx]
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (h j)]
      rw [this]; norm_num
  have hxsum : ∑ k, x k = (b:ℝ) := by
    simp only [hx]
    rw [Finset.sum_comm]
    simp
  have F2 : ∑ k, x k * x k = (b:ℝ) := by
    simp only [hxv]; exact hxsum
  have F3 : ∑ k, s k * x k = (a:ℝ) * b := by
    simp only [hs, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i _ => F1 i)]
    simp
  have e4 : ∀ k, s k * s k = ∑ i, ∑ i', H (rri i) k * H (rri i') k := by
    intro k; simp only [hs, Finset.sum_mul_sum]
  have F4 : ∑ k, s k * s k = (a:ℝ) * n := by
    simp only [e4]
    rw [Finset.sum_comm]
    have step : ∀ i : Fin a, ∑ k, ∑ i', H (rri i) k * H (rri i') k = (n:ℝ) := by
      intro i
      rw [Finset.sum_comm]
      simp only [hrow_sum]
      simp
    rw [Finset.sum_congr rfl (fun i _ => step i)]
    simp
  have key : 0 ≤ ∑ k, (x k - ((b:ℝ)/n) * s k)^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have expand : ∀ k, (x k - ((b:ℝ)/n) * s k)^2 = x k * x k - 2*((b:ℝ)/n) * (s k * x k) + ((b:ℝ)/n)^2 * (s k * s k) := by
    intro k; ring
  simp_rw [expand] at key
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, F2, F3, F4] at key
  have hn : (0:ℝ) < n := by exact_mod_cast npos
  have hb : (0:ℝ) < b := by exact_mod_cast hb1
  field_simp at key
  have : (a:ℝ) * b ≤ n := by nlinarith
  exact_mod_cast this
