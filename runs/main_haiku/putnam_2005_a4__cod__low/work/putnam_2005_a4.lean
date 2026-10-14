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
: a * b ≤ n :=by
  obtain ⟨r, c, hr, hc, hS⟩ := Ssub
  have h1 : ∀ i j, H (r i) (c j) = 1 := by
    intro i j
    have := Sentries i j
    rw [hS] at this
    simpa [Matrix.submatrix] using this
  have hcol : ∀ j : Fin b, ∑ i : Fin a, H (r i) (c j) = (a:ℝ) := by
    intro j; simp [h1]
  set y : Fin n → ℝ := fun k => ∑ i : Fin a, H (r i) k with hydef
  have hone : ∀ i k, H (r i) k * H (r i) k = 1 := by
    intro i k
    rcases Hentries (r i) k with h | h <;> rw [h] <;> norm_num
  have hpair : ∀ i j : Fin a, ∑ k, H (r i) k * H (r j) k = if i = j then (n:ℝ) else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [hone]
    · rw [if_neg h]
      have := Hortho (hr.ne h)
      simpa [dotProduct] using this
  have expand : ∀ k, (y k)^2 = ∑ i, ∑ j, H (r i) k * H (r j) k := by
    intro k; simp only [hydef, sq, Finset.sum_mul_sum]
  have hsq : ∑ k, (y k)^2 = (a:ℝ) * n := by
    rw [Finset.sum_congr rfl (fun k _ => expand k), Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
    simp only [hpair]
    simp
  have hy : ∀ j, y (c j) = a := by
    intro j; simp only [hydef, hcol j]
  have hsub : ∑ j : Fin b, (y (c j))^2 = ∑ k ∈ (Finset.univ.image c), (y k)^2 :=
    by rw [Finset.sum_image (fun x _ z _ h => hc h)]
  have hle : ∑ k ∈ (Finset.univ.image c), (y k)^2 ≤ ∑ k, (y k)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hbig : (b:ℝ) * (a:ℝ)^2 ≤ (a:ℝ) * n := by
    have : ∑ j : Fin b, (y (c j))^2 = (b:ℝ) * (a:ℝ)^2 := by
      simp [hy]
    linarith
  have ha : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have key : (a:ℝ) * b ≤ n := by
    have : (a:ℝ) * ((a:ℝ) * b) ≤ (a:ℝ) * n := by nlinarith
    exact le_of_mul_le_mul_left this ha
  exact_mod_cast key
