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
: a * b ≤ n :=
by
  obtain ⟨r, c, hr, hc, hS⟩ := Ssub
  have hE : ∀ i j, H (r i) (c j) = 1 := by
    intro i j
    have := Sentries i j
    rw [hS] at this
    simpa using this
  set C : Finset (Fin n) := Finset.univ.image c with hCdef
  set χ : Fin n → ℝ := fun j => if j ∈ C then 1 else 0 with hχ
  set A : Fin n → ℝ := fun j => ∑ i, H (r i) j with hA
  have hpt : ∀ j, (A j - (a:ℝ) * χ j) ^ 2
      = A j ^ 2 - 2 * (a:ℝ) * (χ j * A j) + (a:ℝ) ^ 2 * χ j := by
    intro j
    by_cases h : j ∈ C <;> simp [hχ, h] <;> ring
  have hsumA : ∑ j, A j ^ 2 = (a:ℝ) * n := by
    have h1 : ∑ j, A j ^ 2 = ∑ i, ∑ k, ∑ j, H (r i) j * H (r k) j := by
      calc ∑ j, A j ^ 2 = ∑ j, ∑ i, ∑ k, H (r i) j * H (r k) j :=
            Finset.sum_congr rfl fun j _ => by simp only [hA, sq, Finset.sum_mul_sum]
        _ = ∑ i, ∑ j, ∑ k, H (r i) j * H (r k) j := Finset.sum_comm
        _ = ∑ i, ∑ k, ∑ j, H (r i) j * H (r k) j :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [h1]
    have h3 : ∀ i k, ∑ j, H (r i) j * H (r k) j = if i = k then (n:ℝ) else 0 := by
      intro i k
      by_cases hik : i = k
      · subst hik
        have : ∀ j, H (r i) j * H (r i) j = 1 := by
          intro j
          rcases Hentries (r i) j with h | h <;> rw [h] <;> norm_num
        simp [this]
      · have hne : r i ≠ r k := fun h => hik (hr h)
        have := Hortho hne
        simp only [dotProduct] at this
        simp [hik, this]
    simp only [h3]
    simp
  have hsumχA : ∑ j, χ j * A j = (a:ℝ) * b := by
    have h1 : ∀ j, χ j * A j = ∑ i, (if j ∈ C then H (r i) j else 0) := by
      intro j
      simp only [hχ, hA]
      by_cases h : j ∈ C <;> simp [h, Finset.mul_sum]
    simp only [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ i, ∑ j, (if j ∈ C then H (r i) j else 0) = (b:ℝ) := by
      intro i
      rw [← Finset.sum_filter]
      have : Finset.univ.filter (fun j => j ∈ C) = C := by
        ext j; simp
      rw [this, hCdef, Finset.sum_image (fun x _ y _ h => hc h)]
      simp [hE]
    simp only [h2]
    simp
  have hsumχ : ∑ j, χ j = (b:ℝ) := by
    have h0 : ∀ j, χ j = if j ∈ C then (1:ℝ) else 0 := fun j => rfl
    simp only [h0]
    rw [Finset.sum_boole]
    have : Finset.univ.filter (fun j => j ∈ C) = C := by
      ext j; simp
    rw [this, hCdef, Finset.card_image_of_injective _ hc]
    simp
  have e1 : ∑ j, 2 * (a:ℝ) * (χ j * A j) = 2 * (a:ℝ) * (a * b) := by
    rw [← Finset.mul_sum, hsumχA]
  have e2 : ∑ j, (a:ℝ) ^ 2 * χ j = (a:ℝ) ^ 2 * b := by
    rw [← Finset.mul_sum, hsumχ]
  have e3 : ∑ j, (A j ^ 2 - 2 * (a:ℝ) * (χ j * A j) + (a:ℝ) ^ 2 * χ j)
      = ∑ j, A j ^ 2 - ∑ j, 2 * (a:ℝ) * (χ j * A j) + ∑ j, (a:ℝ) ^ 2 * χ j := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hsq : 0 ≤ ∑ j, (A j - (a:ℝ) * χ j) ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  simp only [hpt] at hsq
  rw [e3, e1, e2, hsumA] at hsq
  have ha : (1:ℝ) ≤ a := by exact_mod_cast hab.1
  have key : (a:ℝ) * b ≤ n := by
    have hpos : (0:ℝ) < a := by linarith
    nlinarith
  exact_mod_cast key
