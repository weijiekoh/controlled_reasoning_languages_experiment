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
  have hanti : ∀ x y : Fin 3 → ℝ, x ⨯₃ y = -(y ⨯₃ x) := by
    intro x y; ext j; fin_cases j <;> simp [crossProduct] <;> ring
  have hd1 : ∀ x y : Fin 3 → ℝ, y ⬝ᵥ (x ⨯₃ y) = 0 := by
    intro x y; simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring
  have hd2 : ∀ x y : Fin 3 → ℝ, (x ⨯₃ y) ⬝ᵥ y = 0 := by
    intro x y; simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring
  have hlag : ∀ x y : Fin 3 → ℝ,
      (x ⨯₃ y) ⬝ᵥ (x ⨯₃ y) = (x ⬝ᵥ x) * (y ⬝ᵥ y) - (x ⬝ᵥ y) ^ 2 := by
    intro x y; simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring
  have hbin : ∀ x y z : Fin 3 → ℝ,
      (x ⬝ᵥ y) * (z ⬝ᵥ z) = (x ⬝ᵥ z) * (y ⬝ᵥ z) + (x ⨯₃ z) ⬝ᵥ (y ⨯₃ z) := by
    intro x y z; simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring
  have hbac : ∀ x y : Fin 3 → ℝ, x ⨯₃ (x ⨯₃ y) = (x ⬝ᵥ y) • x - (x ⬝ᵥ x) • y := by
    intro x y; ext j; fin_cases j <;> simp [crossProduct, dotProduct, Fin.sum_univ_three] <;> ring
  have hzero : ∀ x : Fin 3 → ℝ, x ⬝ᵥ x = 0 → x = 0 := by
    intro x hx; simpa using hx
  have hnn : ∀ x : Fin 3 → ℝ, 0 ≤ x ⬝ᵥ x := by
    intro x; simp [dotProduct, Fin.sum_univ_three]; nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_self_nonneg (x 2)]
  have hcz : ∀ x : Fin 3 → ℝ, x ⨯₃ 0 = 0 := by
    intro x; ext j; fin_cases j <;> simp [crossProduct]
  have hz0 : ∀ x : Fin 3 → ℝ, 0 ⨯₃ x = 0 := by
    intro x; ext j; fin_cases j <;> simp [crossProduct]
  have hV2 : ∀ x p q : Fin 3 → ℝ, x ⨯₃ p = 0 → x ⨯₃ q = 0 → p ⨯₃ q ≠ 0 → x = 0 := by
    intro x p q hp hq hn
    have A0 := congrFun hp 0
    have A1 := congrFun hp 1
    have A2 := congrFun hp 2
    have B0 := congrFun hq 0
    have B1 := congrFun hq 1
    have B2 := congrFun hq 2
    simp [crossProduct] at A0 A1 A2 B0 B1 B2
    have hn' : p 1 * q 2 - p 2 * q 1 ≠ 0 ∨ p 2 * q 0 - p 0 * q 2 ≠ 0 ∨
        p 0 * q 1 - p 1 * q 0 ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hn
      ext j
      fin_cases j <;> simp [crossProduct] <;> linarith [hc.1, hc.2.1, hc.2.2]
    rcases hn' with h0 | h1 | h2
    · have e1 : x 1 * (p 1 * q 2 - p 2 * q 1) = 0 := by
        linear_combination p 1 * B0 - q 1 * A0
      have e2 : x 2 * (p 1 * q 2 - p 2 * q 1) = 0 := by
        linear_combination p 2 * B0 - q 2 * A0
      have hx1 : x 1 = 0 := (mul_eq_zero.mp e1).resolve_right h0
      have hx2 : x 2 = 0 := (mul_eq_zero.mp e2).resolve_right h0
      have e0 : x 0 * (p 1 * q 2 - p 2 * q 1) = 0 := by
        linear_combination q 2 * A2 - p 2 * B2 - (p 2 * q 0 - p 0 * q 2) * hx1
      have hx0 : x 0 = 0 := (mul_eq_zero.mp e0).resolve_right h0
      ext j; fin_cases j <;> simp [hx0, hx1, hx2]
    · have e1 : x 2 * (p 2 * q 0 - p 0 * q 2) = 0 := by
        linear_combination p 2 * B1 - q 2 * A1
      have e2 : x 0 * (p 2 * q 0 - p 0 * q 2) = 0 := by
        linear_combination p 0 * B1 - q 0 * A1
      have hx2 : x 2 = 0 := (mul_eq_zero.mp e1).resolve_right h1
      have hx0 : x 0 = 0 := (mul_eq_zero.mp e2).resolve_right h1
      have e0 : x 1 * (p 2 * q 0 - p 0 * q 2) = 0 := by
        linear_combination q 0 * A0 - p 0 * B0 - (p 0 * q 1 - p 1 * q 0) * hx2
      have hx1 : x 1 = 0 := (mul_eq_zero.mp e0).resolve_right h1
      ext j; fin_cases j <;> simp [hx0, hx1, hx2]
    · have e1 : x 0 * (p 0 * q 1 - p 1 * q 0) = 0 := by
        linear_combination p 0 * B2 - q 0 * A2
      have e2 : x 1 * (p 0 * q 1 - p 1 * q 0) = 0 := by
        linear_combination p 1 * B2 - q 1 * A2
      have hx0 : x 0 = 0 := (mul_eq_zero.mp e1).resolve_right h2
      have hx1 : x 1 = 0 := (mul_eq_zero.mp e2).resolve_right h2
      have e0 : x 2 * (p 0 * q 1 - p 1 * q 0) = 0 := by
        linear_combination q 1 * A1 - p 1 * B1 - (p 1 * q 2 - p 2 * q 1) * hx0
      have hx2 : x 2 = 0 := (mul_eq_zero.mp e0).resolve_right h2
      ext j; fin_cases j <;> simp [hx0, hx1, hx2]
  -- main argument
  have hne_proof : ∀ (hne : ¬ (i a ⨯₃ i b = 0)), False := by
    intro hne
    have hid : ∀ g : G, i 1 ⨯₃ i g = 0 := by
      intro g
      rcases h 1 g with h1 | h1
      · rw [one_mul] at h1
        have d := hd1 (i 1) (i g)
        rw [h1] at d
        have hz := hzero _ d
        rw [hz]; exact hcz _
      · exact h1
    have hu0 : i 1 = 0 := hV2 _ _ _ (hid a) (hid b) hne
    have hinv : ∀ g : G, i g ⨯₃ i g⁻¹ = 0 := by
      intro g
      rcases h g g⁻¹ with h1 | h1
      · rw [mul_inv_cancel, hu0] at h1; exact h1
      · exact h1
    have hab_eq : i (a * b) = i a ⨯₃ i b := by
      rcases h a b with h1 | h1
      · exact h1.symm
      · exact absurd h1 hne
    have hia : i a ≠ 0 := fun h0 => hne (by rw [h0]; exact hz0 _)
    have hib : i b ≠ 0 := fun h0 => hne (by rw [h0]; exact hcz _)
    have hbv := hinv b
    have hc1 := h (a * b) b⁻¹
    rw [mul_inv_cancel_right, hab_eq] at hc1
    rcases hc1 with hc | hc
    swap
    · -- C ⨯ v = 0 leads to contradiction
      have hvz : i b⁻¹ = 0 := by
        apply hV2 _ (i b) (i a ⨯₃ i b)
        · rw [hanti, hbv, neg_zero]
        · rw [hanti, hc, neg_zero]
        · intro h0
          have hbC : i b ⬝ᵥ (i a ⨯₃ i b) = 0 := hd1 _ _
          have h2 := hlag (i b) (i a ⨯₃ i b)
          rw [h0, hbC] at h2
          rw [zero_dotProduct] at h2
          have h3 : (i b ⬝ᵥ i b) * ((i a ⨯₃ i b) ⬝ᵥ (i a ⨯₃ i b)) = 0 := by linarith
          rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hib (hzero _ h4)
          · exact hne (hzero _ h4)
      have hb1 : b⁻¹ = 1 := i.injective (show i b⁻¹ = i 1 by rw [hu0]; exact hvz)
      have hb : b = 1 := inv_eq_one.mp hb1
      exact hib (by rw [hb, hu0])
    · -- hc : C ⨯ v = i a
      have hsum := hc.symm
      have hdva : i a ⬝ᵥ i b⁻¹ = 0 := by
        rw [hsum]; exact hd2 _ _
      have hvne : i b⁻¹ ≠ 0 := by
        intro h0
        apply hia
        rw [← hc, h0, hcz]
      have hab : i a ⬝ᵥ i b = 0 := by
        have k1 := hbin (i a) (i b) (i b⁻¹)
        rw [hbv, hdva] at k1
        simp only [zero_mul, dotProduct_zero, zero_add] at k1
        rcases mul_eq_zero.mp k1 with k | k
        · exact k
        · exact absurd (hzero _ k) hvne
      -- squares commute
      have hsq : ∀ x : G, i (x * x) ⨯₃ i x = 0 := by
        intro x
        have e : x * (x * x) = x * x * x := (mul_assoc x x x).symm
        have A := h (x * x) x
        have B := h x (x * x)
        rw [e] at B
        rw [hanti (i x) (i (x * x))] at B
        rcases A with A | A
        · rcases B with B | B
          · ext j
            have e1 := congrFun A j
            have e2 := congrFun B j
            simp only [Pi.neg_apply] at e2
            simp only [Pi.zero_apply]
            linarith
          · ext j
            have e1 := congrFun B j
            simp only [Pi.neg_apply, Pi.zero_apply] at e1
            simp only [Pi.zero_apply]
            linarith
        · exact A
      have hs_a := hsq a
      have hk : i a ⬝ᵥ i a ≠ 0 := fun h0 => hia (hzero _ h0)
      have hac := h a (a * b)
      rw [hab_eq, hbac, hab, zero_smul, zero_sub] at hac
      have hac' : i (a * (a * b)) = -((i a ⬝ᵥ i a) • i b) := by
        rcases hac with h1 | h1
        · exact h1.symm
        · exact absurd h1 (neg_ne_zero.mpr (smul_ne_zero hk hib))
      have hh := h (a * a) b
      rw [mul_assoc, hac'] at hh
      rcases hh with h1 | h1
      · have d := hd2 (i (a * a)) (i b)
        rw [h1] at d
        have d2 : (i a ⬝ᵥ i a) * (i b ⬝ᵥ i b) = 0 := by
          simp only [neg_dotProduct, smul_dotProduct, smul_eq_mul] at d
          linarith
        rcases mul_eq_zero.mp d2 with k0 | k0
        · exact hk k0
        · exact hib (hzero _ k0)
      · have hs0 : i (a * a) = 0 := hV2 _ _ _ hs_a h1 hne
        have haa : a * a = 1 := i.injective (by rw [hs0, hu0])
        have hb' : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
        rw [hb'] at hac'
        have h7 := eq_neg_iff_add_eq_zero.mp hac'
        have h5 : (1 + (i a ⬝ᵥ i a)) • i b = 0 := by
          rw [add_smul, one_smul]; exact h7
        rcases smul_eq_zero.mp h5 with h6 | h6
        · have := hnn (i a); linarith
        · exact hib h6
  by_contra hne
  exact hne_proof hne
