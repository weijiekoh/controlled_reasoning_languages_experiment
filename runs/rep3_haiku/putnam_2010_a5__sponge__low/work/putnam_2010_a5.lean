import Mathlib

open scoped Matrix

/--
Let $G$ be a group, with operation $*$. Suppose that \begin{enumerate} \item[(i)] $G$ is a subset of $\mathbb{R}^3$ (but $*$ need not be related to addition of vectors); \item[(ii)] For each $\mathbf{a},\mathbf{b} \in G$, either $\mathbf{a}\times \mathbf{b} = \mathbf{a}*\mathbf{b}$ or $\mathbf{a}\times \mathbf{b} = 0$ (or both), where $\times$ is the usual cross product in $\mathbb{R}^3$. \end{enumerate} Prove that $\mathbf{a} \times \mathbf{b} = 0$ for all $\mathbf{a}, \mathbf{b} \in G$.
-/
theorem putnam_2010_a5
    (G : Type*) [Group G]
    (i : G ↪ (Fin 3 → ℝ))
    (h : ∀ a b, (i a) ⨯₃ (i b) = i (a * b) ∨ (i a) ⨯₃ (i b) = 0)
    (a b : G) :
    (i a) ⨯₃ (i b) = 0 := by
  classical
  have c0 : ∀ X Y : Fin 3 → ℝ, (X ⨯₃ Y) 0 = X 1 * Y 2 - X 2 * Y 1 := by
    intro X Y; rw [cross_apply]; simp
  have c1 : ∀ X Y : Fin 3 → ℝ, (X ⨯₃ Y) 1 = X 2 * Y 0 - X 0 * Y 2 := by
    intro X Y; rw [cross_apply]; simp
  have c2 : ∀ X Y : Fin 3 → ℝ, (X ⨯₃ Y) 2 = X 0 * Y 1 - X 1 * Y 0 := by
    intro X Y; rw [cross_apply]; simp
  have hz : ∀ X : Fin 3 → ℝ, X = 0 ↔ (X 0 = 0 ∧ X 1 = 0 ∧ X 2 = 0) := by
    intro X; constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1, h2⟩; funext k; fin_cases k <;> simp [h0, h1, h2]
  have hcz : ∀ X Y : Fin 3 → ℝ, X ⨯₃ Y = 0 ↔
      (X 1 * Y 2 - X 2 * Y 1 = 0 ∧ X 2 * Y 0 - X 0 * Y 2 = 0 ∧ X 0 * Y 1 - X 1 * Y 0 = 0) := by
    intro X Y; rw [hz]; simp only [c0, c1, c2]
  have hdot : ∀ X : Fin 3 → ℝ, X ≠ 0 → 0 < X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 := by
    intro X hX
    by_contra hc
    push_neg at hc
    have h0 : X 0 ^ 2 = 0 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (X 2)]
    have h1 : X 1 ^ 2 = 0 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (X 2)]
    have h2 : X 2 ^ 2 = 0 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (X 2)]
    exact hX ((hz X).2 ⟨(pow_eq_zero_iff two_ne_zero).mp h0,
      (pow_eq_zero_iff two_ne_zero).mp h1, (pow_eq_zero_iff two_ne_zero).mp h2⟩)
  have L : ∀ x y : G, i x ⨯₃ i y ≠ 0 → i x ⨯₃ i y = i (x * y) := by
    intro x y hxy
    rcases h x y with h1 | h1
    · exact h1
    · exact absurd h1 hxy
  have PL : ∀ E A B : Fin 3 → ℝ, E ≠ 0 → E ⨯₃ A = 0 → E ⨯₃ B = 0 → A ⨯₃ B = 0 := by
    intro E A B hE hA hB
    obtain ⟨eA0, eA1, eA2⟩ := (hcz E A).1 hA
    obtain ⟨eB0, eB1, eB2⟩ := (hcz E B).1 hB
    have key : E 0 ≠ 0 ∨ E 1 ≠ 0 ∨ E 2 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hE ((hz E).2 hc)
    rw [hcz]
    rcases key with h0 | h1 | h2
    · have a1 : A 1 = E 1 * A 0 / E 0 := (eq_div_iff h0).2 (by linear_combination eA2)
      have a2 : A 2 = E 2 * A 0 / E 0 := (eq_div_iff h0).2 (by linear_combination (-1:ℝ) * eA1)
      have b1 : B 1 = E 1 * B 0 / E 0 := (eq_div_iff h0).2 (by linear_combination eB2)
      have b2 : B 2 = E 2 * B 0 / E 0 := (eq_div_iff h0).2 (by linear_combination (-1:ℝ) * eB1)
      refine ⟨?_, ?_, ?_⟩ <;> simp only [a1, a2, b1, b2] <;> ring
    · have a0 : A 0 = E 0 * A 1 / E 1 := (eq_div_iff h1).2 (by linear_combination (-1:ℝ) * eA2)
      have a2 : A 2 = E 2 * A 1 / E 1 := (eq_div_iff h1).2 (by linear_combination eA0)
      have b0 : B 0 = E 0 * B 1 / E 1 := (eq_div_iff h1).2 (by linear_combination (-1:ℝ) * eB2)
      have b2 : B 2 = E 2 * B 1 / E 1 := (eq_div_iff h1).2 (by linear_combination eB0)
      refine ⟨?_, ?_, ?_⟩ <;> simp only [a0, a2, b0, b2] <;> ring
    · have a0 : A 0 = E 0 * A 2 / E 2 := (eq_div_iff h2).2 (by linear_combination eA1)
      have a1 : A 1 = E 1 * A 2 / E 2 := (eq_div_iff h2).2 (by linear_combination (-1:ℝ) * eA0)
      have b0 : B 0 = E 0 * B 2 / E 2 := (eq_div_iff h2).2 (by linear_combination eB1)
      have b1 : B 1 = E 1 * B 2 / E 2 := (eq_div_iff h2).2 (by linear_combination (-1:ℝ) * eB0)
      refine ⟨?_, ?_, ?_⟩ <;> simp only [a0, a1, b0, b1] <;> ring
  by_contra hN
  by_cases hE : i 1 = 0
  · have hAB : i (a * b) = i a ⨯₃ i b := (L a b hN).symm
    have hpos := hdot (i a ⨯₃ i b) hN
    have hAne : i a ≠ 0 := by
      intro h0; apply hN; rw [hcz]; simp [h0]
    have hAA := hdot (i a) hAne
    have idW : (i a ⨯₃ i b) 0 ^ 2 + (i a ⨯₃ i b) 1 ^ 2 + (i a ⨯₃ i b) 2 ^ 2
        = -((i a ⨯₃ (i a ⨯₃ i b)) 0 * i b 0 + (i a ⨯₃ (i a ⨯₃ i b)) 1 * i b 1
            + (i a ⨯₃ (i a ⨯₃ i b)) 2 * i b 2) := by
      simp only [c0, c1, c2]; ring
    have idX : (i a ⨯₃ (i a ⨯₃ (i a ⨯₃ i b))) 0 * (i a ⨯₃ i b) 0
        + (i a ⨯₃ (i a ⨯₃ (i a ⨯₃ i b))) 1 * (i a ⨯₃ i b) 1
        + (i a ⨯₃ (i a ⨯₃ (i a ⨯₃ i b))) 2 * (i a ⨯₃ i b) 2
        = -((i a 0 ^ 2 + i a 1 ^ 2 + i a 2 ^ 2) *
            ((i a ⨯₃ i b) 0 ^ 2 + (i a ⨯₃ i b) 1 ^ 2 + (i a ⨯₃ i b) 2 ^ 2)) := by
      simp only [c0, c1, c2]; ring
    have hW : i a ⨯₃ (i a ⨯₃ i b) ≠ 0 := by
      intro hz0
      rw [hz0] at idW
      simp only [Pi.zero_apply, zero_mul, add_zero, neg_zero] at idW
      linarith
    have hWA : i a ⨯₃ (i a ⨯₃ (i a ⨯₃ i b)) ≠ 0 := by
      intro hz0
      rw [hz0] at idX
      simp only [Pi.zero_apply, zero_mul, add_zero] at idX
      nlinarith [mul_pos hAA hpos]
    have hL2 : i a ⨯₃ (i a ⨯₃ i b) = i (a * (a * b)) := by
      have hne : i a ⨯₃ i (a * b) ≠ 0 := by rw [hAB]; exact hW
      have := L a (a * b) hne
      rw [hAB] at this
      exact this
    have hL3 : i a ⨯₃ (i a ⨯₃ (i a ⨯₃ i b)) = i (a * (a * (a * b))) := by
      have hne : i a ⨯₃ i (a * (a * b)) ≠ 0 := by rw [← hL2]; exact hWA
      have := L a (a * (a * b)) hne
      rw [← hL2] at this
      exact this
    have hV1 : i (a * a) ⨯₃ i b = 0 := by
      rcases h (a * a) b with h1 | h1
      · exfalso
        rw [mul_assoc, ← hL2] at h1
        have idV : (i (a * a) ⨯₃ i b) 0 * i b 0 + (i (a * a) ⨯₃ i b) 1 * i b 1
            + (i (a * a) ⨯₃ i b) 2 * i b 2 = 0 := by
          simp only [c0, c1, c2]; ring
        rw [h1] at idV
        linarith
      · exact h1
    have hV2 : i (a * a) ⨯₃ (i a ⨯₃ i b) = 0 := by
      rcases h (a * a) (a * b) with h1 | h1
      · exfalso
        rw [hAB, mul_assoc, ← hL3] at h1
        have idV2 : (i (a * a) ⨯₃ (i a ⨯₃ i b)) 0 * (i a ⨯₃ i b) 0
            + (i (a * a) ⨯₃ (i a ⨯₃ i b)) 1 * (i a ⨯₃ i b) 1
            + (i (a * a) ⨯₃ (i a ⨯₃ i b)) 2 * (i a ⨯₃ i b) 2 = 0 := by
          simp only [c0, c1, c2]; ring
        rw [h1] at idV2
        linarith [mul_pos hAA hpos]
      · rw [hAB] at h1; exact h1
    have hV0 : i (a * a) = 0 := by
      by_contra hV0
      have hbN := PL _ _ _ hV0 hV1 hV2
      have idBN : (i b ⨯₃ (i a ⨯₃ i b)) 0 * i a 0 + (i b ⨯₃ (i a ⨯₃ i b)) 1 * i a 1
          + (i b ⨯₃ (i a ⨯₃ i b)) 2 * i a 2
          = (i a ⨯₃ i b) 0 ^ 2 + (i a ⨯₃ i b) 1 ^ 2 + (i a ⨯₃ i b) 2 ^ 2 := by
        simp only [c0, c1, c2]; ring
      rw [hbN] at idBN
      simp only [Pi.zero_apply, zero_mul, add_zero] at idBN
      linarith
    have haa : a * a = 1 := i.injective (by rw [hV0, hE])
    have hb : i (a * (a * b)) = i b := by rw [← mul_assoc, haa, one_mul]
    have hWB : i a ⨯₃ (i a ⨯₃ i b) = i b := by rw [hL2, hb]
    rw [hWB] at idW
    nlinarith [mul_self_nonneg (i b 0), mul_self_nonneg (i b 1), mul_self_nonneg (i b 2)]
  · have key : ∀ x : G, i x ≠ 0 → i 1 ⨯₃ i x = 0 := by
      intro x hx
      by_contra hc
      have h1 : i 1 ⨯₃ i x = i x := by
        rcases h 1 x with h1 | h1
        · rw [one_mul] at h1; exact h1
        · exact absurd h1 hc
      have e0 : (i 1 ⨯₃ i x) 0 = i x 0 := by rw [h1]
      have e1 : (i 1 ⨯₃ i x) 1 = i x 1 := by rw [h1]
      have e2 : (i 1 ⨯₃ i x) 2 = i x 2 := by rw [h1]
      rw [c0] at e0
      rw [c1] at e1
      rw [c2] at e2
      have s : i x 0 ^ 2 + i x 1 ^ 2 + i x 2 ^ 2 = 0 := by
        linear_combination (-(i x 0)) * e0 + (-(i x 1)) * e1 + (-(i x 2)) * e2
      linarith [hdot (i x) hx]
    have kA : i 1 ⨯₃ i a = 0 := by
      by_cases hA : i a = 0
      · rw [hcz]; simp [hA]
      · exact key a hA
    have kB : i 1 ⨯₃ i b = 0 := by
      by_cases hB : i b = 0
      · rw [hcz]; simp [hB]
      · exact key b hB
    exact hN (PL _ _ _ hE kA kB)
