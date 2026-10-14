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
  -- bilinearity and basic facts, by coordinates
  have hsL : ∀ (r : ℝ) (u v : Fin 3 → ℝ), (r • u) ⨯₃ v = r • (u ⨯₃ v) := by
    intro r u v; funext j; fin_cases j <;> simp [cross_apply] <;> ring
  have hsR : ∀ (r : ℝ) (u v : Fin 3 → ℝ), u ⨯₃ (r • v) = r • (u ⨯₃ v) := by
    intro r u v; funext j; fin_cases j <;> simp [cross_apply] <;> ring
  -- parallel lemma: nonzero u, u × v = 0 gives v = k u
  have par : ∀ u v : Fin 3 → ℝ, u ≠ 0 → u ⨯₃ v = 0 → ∃ k : ℝ, v = k • u := by
    intro u v hu hc
    have c0 := congrFun hc 0
    have c1 := congrFun hc 1
    have c2 := congrFun hc 2
    simp [cross_apply] at c0 c1 c2
    have hu' : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hu
      funext j; fin_cases j <;> simp [hcon.1, hcon.2.1, hcon.2.2]
    rcases hu' with h0 | h1 | h2
    · refine ⟨v 0 / u 0, ?_⟩
      funext j; fin_cases j <;> simp <;> field_simp <;> linarith
    · refine ⟨v 1 / u 1, ?_⟩
      funext j; fin_cases j <;> simp <;> field_simp <;> linarith
    · refine ⟨v 2 / u 2, ?_⟩
      funext j; fin_cases j <;> simp <;> field_simp <;> linarith
  have hdz : ∀ v : Fin 3 → ℝ, v ⬝ᵥ v = 0 → v = 0 := fun v hv =>
    dotProduct_self_eq_zero.mp hv
  have hcr : ∀ g g' : G, (i g) ⨯₃ (i g') ≠ 0 → i (g * g') = (i g) ⨯₃ (i g') := by
    intro g g' hne
    exact ((h g g').resolve_right hne).symm
  by_contra hne
  have hA0 : i a ≠ 0 := by
    intro h0; apply hne; rw [h0]; funext j; fin_cases j <;> simp [cross_apply]
  have hB0 : i b ≠ 0 := by
    intro h0; apply hne; rw [h0]; funext j; fin_cases j <;> simp [cross_apply]
  by_cases he : i 1 = 0
  · have hAB : i (a * b) = i a ⨯₃ i b := hcr a b hne
    -- A × C ≠ 0, with C = A × B
    have hAC : i a ⨯₃ (i a ⨯₃ i b) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := par (i a) (i a ⨯₃ i b) hA0 h0
      have hd := dot_self_cross (i a) (i b)
      rw [hk, dotProduct_smul, smul_eq_mul] at hd
      rcases mul_eq_zero.mp hd with hk0 | hm
      · apply hne; rw [hk, hk0, zero_smul]
      · exact hA0 (hdz _ hm)
    -- inverse of a is parallel to a
    have hAU : i a ⨯₃ i a⁻¹ = 0 := by
      rcases h a a⁻¹ with h1 | h1
      · rw [mul_inv_cancel, he] at h1; exact h1
      · exact h1
    obtain ⟨lam, hlam⟩ := par (i a) (i a⁻¹) hA0 hAU
    have hU0 : i a⁻¹ ≠ 0 := by
      intro h0
      have e1 : a⁻¹ = 1 := by apply i.injective; rw [h0, he]
      have e2 : a = 1 := inv_eq_one.mp e1
      apply hA0; rw [e2, he]
    have hlam0 : lam ≠ 0 := by
      rintro rfl; apply hU0; rw [hlam, zero_smul]
    have hUC : i a⁻¹ ⨯₃ (i a ⨯₃ i b) ≠ 0 := by
      rw [hlam, hsL]; exact smul_ne_zero hlam0 hAC
    have hBU := hcr a⁻¹ (a * b) (by rw [hAB]; exact hUC)
    rw [inv_mul_cancel_left, hAB] at hBU
    rw [hlam, hsL] at hBU
    -- hBU : i b = lam • (A × (A × B))
    have hAB0 : i a ⬝ᵥ i b = 0 := by
      have h1 := dot_self_cross (i a) (i a ⨯₃ i b)
      rw [hBU, dotProduct_smul, h1, smul_zero]
    have hD : i a ⨯₃ (i a ⨯₃ i b) = -((i a ⬝ᵥ i a) • i b) := by
      have hid : ∀ u v : Fin 3 → ℝ, u ⨯₃ (u ⨯₃ v) = (u ⬝ᵥ v) • u - (u ⬝ᵥ u) • v := by
        intro u v; funext j
        fin_cases j <;> simp [cross_apply, dotProduct, Fin.sum_univ_three] <;> ring
      rw [hid, hAB0, zero_smul, zero_sub]
    have hlm : lam * (i a ⬝ᵥ i a) = -1 := by
      have hBU2 := hBU
      rw [hD] at hBU2
      have h3 : (lam * -(i a ⬝ᵥ i a)) • i b = i b := by
        calc (lam * -(i a ⬝ᵥ i a)) • i b = lam • (-(i a ⬝ᵥ i a) • i b) := (smul_smul _ _ _).symm
          _ = lam • -((i a ⬝ᵥ i a) • i b) := by rw [neg_smul]
          _ = i b := hBU2.symm
      have h4 : (lam * -(i a ⬝ᵥ i a) - 1) • i b = 0 := by
        rw [sub_smul, one_smul, h3, sub_self]
      rcases smul_eq_zero.mp h4 with h5 | h5
      · linear_combination -h5
      · exact absurd h5 hB0
    have hD2 : i ((a * a) * b) = i a ⨯₃ (i a ⨯₃ i b) := by
      rw [mul_assoc, hcr a (a * b) (by rw [hAB]; exact hAC), hAB]
    have hSB : i (a * a) ⨯₃ i b = 0 := by
      rcases h (a * a) b with h1 | h1
      · exfalso
        have hd := dot_cross_self (i (a * a)) (i b)
        rw [h1, hD2, hD, dotProduct_neg, dotProduct_smul, smul_eq_mul] at hd
        have hm : (i a ⬝ᵥ i a) * (i b ⬝ᵥ i b) = 0 := by linarith
        rcases mul_eq_zero.mp hm with hm1 | hm1
        · exact hA0 (hdz _ hm1)
        · exact hB0 (hdz _ hm1)
      · exact h1
    have hSU := h (a * a) a⁻¹
    have hSA : i (a * a) ⨯₃ i a = 0 := by
      rcases hSU with h1 | h1
      · rw [mul_inv_cancel_right] at h1
        have hd := dot_cross_self (i (a * a)) (i a⁻¹)
        rw [h1, hlam, smul_dotProduct, smul_eq_mul] at hd
        exfalso
        have : lam * (i a ⬝ᵥ i a) = 0 := by linarith
        linarith
      · rw [hlam, hsR] at h1
        rcases smul_eq_zero.mp h1 with h2 | h2
        · exact absurd h2 hlam0
        · exact h2
    have hAS : i a ⨯₃ i (a * a) = 0 := by
      rw [← cross_anticomm, hSA, neg_zero]
    obtain ⟨t, ht⟩ := par (i a) (i (a * a)) hA0 hAS
    have hS0 : i (a * a) = 0 := by
      rw [ht, hsL] at hSB
      rcases smul_eq_zero.mp hSB with ht0 | hc
      · rw [ht, ht0, zero_smul]
      · exact absurd hc hne
    have hAA1 : a * a = 1 := by
      apply i.injective; rw [hS0, he]
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right hAA1
    have hl1 : lam = 1 := by
      have h6 : lam • i a = i a := by rw [← hlam, hainv]
      have h7 : (lam - 1) • i a = 0 := by rw [sub_smul, one_smul, h6, sub_self]
      rcases smul_eq_zero.mp h7 with h8 | h8
      · linarith
      · exact absurd h8 hA0
    rw [hl1] at hlm
    have hnn : 0 ≤ i a ⬝ᵥ i a := by
      simp only [dotProduct, Fin.sum_univ_three]
      nlinarith [mul_self_nonneg (i a 0), mul_self_nonneg (i a 1), mul_self_nonneg (i a 2)]
    linarith
  · have one_cross : ∀ x : G, i 1 ⨯₃ i x = 0 := by
      intro x
      by_contra hx
      have h1 := hcr 1 x hx
      rw [one_mul] at h1
      have hX : i x ≠ 0 := by
        intro h0; apply hx; rw [h0]; funext j; fin_cases j <;> simp [cross_apply]
      have hx' : i x ⨯₃ i 1 ≠ 0 := by
        rw [← cross_anticomm]; exact neg_ne_zero.mpr hx
      have h2 := hcr x 1 hx'
      rw [mul_one, ← cross_anticomm, ← h1] at h2
      apply hX
      funext j
      have := congrFun h2 j
      simp only [Pi.neg_apply] at this
      show i x j = 0
      linarith
    obtain ⟨k, hk⟩ := par (i 1) (i a) he (one_cross a)
    obtain ⟨l, hl⟩ := par (i 1) (i b) he (one_cross b)
    apply hne
    rw [hk, hl, hsL, hsR]
    have hcc : i 1 ⨯₃ i 1 = 0 := by
      funext j; fin_cases j <;> simp [cross_apply]
    rw [hcc]; simp
