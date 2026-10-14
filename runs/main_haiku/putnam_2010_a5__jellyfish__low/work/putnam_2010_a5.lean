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
    (i a) ⨯₃ (i b) = 0 :=
  by
  by_contra hW
  have hc0 : ∀ X Y : Fin 3 → ℝ, (X ⨯₃ Y) 0 = X 1 * Y 2 - X 2 * Y 1 := fun X Y => by
    simp [cross_apply]
  have hc1 : ∀ X Y : Fin 3 → ℝ, (X ⨯₃ Y) 1 = X 2 * Y 0 - X 0 * Y 2 := fun X Y => by
    simp [cross_apply]
  have hc2 : ∀ X Y : Fin 3 → ℝ, (X ⨯₃ Y) 2 = X 0 * Y 1 - X 1 * Y 0 := fun X Y => by
    simp [cross_apply]
  have hext : ∀ X Y : Fin 3 → ℝ, X = Y ↔ (X 0 = Y 0 ∧ X 1 = Y 1 ∧ X 2 = Y 2) := by
    intro X Y
    constructor
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨h0, h1, h2⟩
      funext j
      fin_cases j <;> simp [h0, h1, h2]
  have hnz : ∀ X : Fin 3 → ℝ, X ≠ 0 → 0 < X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 := by
    intro X hX
    by_contra hle
    push_neg at hle
    apply hX
    have e0 : X 0 ^ 2 = 0 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (X 2)]
    have e1 : X 1 ^ 2 = 0 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (X 2)]
    have e2 : X 2 ^ 2 = 0 := by nlinarith [sq_nonneg (X 0), sq_nonneg (X 1), sq_nonneg (X 2)]
    have h0 := (pow_eq_zero_iff two_ne_zero).1 e0
    have h1 := (pow_eq_zero_iff two_ne_zero).1 e1
    have h2 := (pow_eq_zero_iff two_ne_zero).1 e2
    funext j
    fin_cases j <;> simp [h0, h1, h2]
  have key0 : ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 p0 p1 p2 q0 q1 q2 w0 w1 w2 : ℝ,
      w0 = a1*b2 - a2*b1 → w1 = a2*b0 - a0*b2 → w2 = a0*b1 - a1*b0 →
      a0^2+a1^2+a2^2 ≠ 0 → b0^2+b1^2+b2^2 ≠ 0 → c0^2+c1^2+c2^2 ≠ 0 →
      w0^2+w1^2+w2^2 ≠ 0 →
      a1*c2 - a2*c1 = 0 → a2*c0 - a0*c2 = 0 → a0*c1 - a1*c0 = 0 →
      ((c1*w2 - c2*w1 = b0 ∧ c2*w0 - c0*w2 = b1 ∧ c0*w1 - c1*w0 = b2) ∨
        (c1*w2 - c2*w1 = 0 ∧ c2*w0 - c0*w2 = 0 ∧ c0*w1 - c1*w0 = 0)) →
      ((a1*w2 - a2*w1 = q0 ∧ a2*w0 - a0*w2 = q1 ∧ a0*w1 - a1*w0 = q2) ∨
        (a1*w2 - a2*w1 = 0 ∧ a2*w0 - a0*w2 = 0 ∧ a0*w1 - a1*w0 = 0)) →
      ((p1*b2 - p2*b1 = q0 ∧ p2*b0 - p0*b2 = q1 ∧ p0*b1 - p1*b0 = q2) ∨
        (p1*b2 - p2*b1 = 0 ∧ p2*b0 - p0*b2 = 0 ∧ p0*b1 - p1*b0 = 0)) →
      ((c1*p2 - c2*p1 = a0 ∧ c2*p0 - c0*p2 = a1 ∧ c0*p1 - c1*p0 = a2) ∨
        (c1*p2 - c2*p1 = 0 ∧ c2*p0 - c0*p2 = 0 ∧ c0*p1 - c1*p0 = 0)) →
      ((p0 = 0 ∧ p1 = 0 ∧ p2 = 0) → (q0 = b0 ∧ q1 = b1 ∧ q2 = b2)) → False := by
    intro a0 a1 a2 b0 b1 b2 c0 c1 c2 p0 p1 p2 q0 q1 q2 w0 w1 w2 hw0 hw1 hw2 hNA hNB hNC hNW
      hAC0 hAC1 hAC2 hDa hQ hPB hCP hZ
    subst hw0 hw1 hw2
    obtain ⟨lam, rfl, rfl, rfl⟩ : ∃ lam, c0 = lam*a0 ∧ c1 = lam*a1 ∧ c2 = lam*a2 := by
      refine ⟨(a0*c0+a1*c1+a2*c2)/(a0^2+a1^2+a2^2), ?_, ?_, ?_⟩
      · field_simp
        linear_combination (-a1)*hAC2 + a2*hAC1
      · field_simp
        linear_combination a0*hAC2 - a2*hAC0
      · field_simp
        linear_combination (-a0)*hAC1 + a1*hAC0
    have hlam : lam ≠ 0 := by
      rintro rfl
      apply hNC
      simp
    rcases hDa with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · have hAB : a0*b0 + a1*b1 + a2*b2 = 0 := by
        linear_combination (-a0)*e0 - a1*e1 - a2*e2
      have hlN : lam*(a0^2+a1^2+a2^2) = -1 := by
        have h' : (b0^2+b1^2+b2^2) * (lam*(a0^2+a1^2+a2^2) + 1) = 0 := by
          linear_combination (-b0)*e0 - b1*e1 - b2*e2 + lam*(a0*b0+a1*b1+a2*b2)*hAB
        have := (mul_eq_zero.mp h').resolve_left hNB
        linarith
      rcases hQ with ⟨f0, f1, f2⟩ | ⟨f0, f1, f2⟩
      · have hq0 : q0 = -(a0^2+a1^2+a2^2)*b0 := by
          linear_combination (-1)*f0 + a0*hAB
        have hq1 : q1 = -(a0^2+a1^2+a2^2)*b1 := by
          linear_combination (-1)*f1 + a1*hAB
        have hq2 : q2 = -(a0^2+a1^2+a2^2)*b2 := by
          linear_combination (-1)*f2 + a2*hAB
        subst hq0 hq1 hq2
        rcases hPB with ⟨g0, g1, g2⟩ | ⟨g0, g1, g2⟩
        · have hfin : (a0^2+a1^2+a2^2)*(b0^2+b1^2+b2^2) = 0 := by
            linear_combination b0*g0 + b1*g1 + b2*g2
          rcases mul_eq_zero.mp hfin with h | h
          · exact hNA h
          · exact hNB h
        · rcases hCP with ⟨k0, k1, k2⟩ | ⟨k0, k1, k2⟩
          · apply hNA
            linear_combination (-a0)*k0 - a1*k1 - a2*k2
          · have m0 : a1*p2 - a2*p1 = 0 := by
              have : lam*(a1*p2 - a2*p1) = 0 := by linear_combination k0
              exact (mul_eq_zero.mp this).resolve_left hlam
            have m1 : a2*p0 - a0*p2 = 0 := by
              have : lam*(a2*p0 - a0*p2) = 0 := by linear_combination k1
              exact (mul_eq_zero.mp this).resolve_left hlam
            have m2 : a0*p1 - a1*p0 = 0 := by
              have : lam*(a0*p1 - a1*p0) = 0 := by linear_combination k2
              exact (mul_eq_zero.mp this).resolve_left hlam
            have hpk0 : (a0^2+a1^2+a2^2)*p0 = (a0*p0+a1*p1+a2*p2)*a0 := by
              linear_combination (-a1)*m2 + a2*m1
            have hpk1 : (a0^2+a1^2+a2^2)*p1 = (a0*p0+a1*p1+a2*p2)*a1 := by
              linear_combination a0*m2 - a2*m0
            have hpk2 : (a0^2+a1^2+a2^2)*p2 = (a0*p0+a1*p1+a2*p2)*a2 := by
              linear_combination (-a0)*m1 + a1*m0
            have hT0 : (a0*p0+a1*p1+a2*p2)*(a1*b2 - a2*b1) = 0 := by
              linear_combination (a0^2+a1^2+a2^2)*g0 - b2*hpk1 + b1*hpk2
            have hT1 : (a0*p0+a1*p1+a2*p2)*(a2*b0 - a0*b2) = 0 := by
              linear_combination (a0^2+a1^2+a2^2)*g1 - b0*hpk2 + b2*hpk0
            have hT2 : (a0*p0+a1*p1+a2*p2)*(a0*b1 - a1*b0) = 0 := by
              linear_combination (a0^2+a1^2+a2^2)*g2 - b1*hpk0 + b0*hpk1
            have hTW : (a0*p0+a1*p1+a2*p2) * ((a1*b2-a2*b1)^2 + (a2*b0-a0*b2)^2
                + (a0*b1-a1*b0)^2) = 0 := by
              linear_combination (a1*b2-a2*b1)*hT0 + (a2*b0-a0*b2)*hT1 + (a0*b1-a1*b0)*hT2
            have ht : a0*p0+a1*p1+a2*p2 = 0 := (mul_eq_zero.mp hTW).resolve_right hNW
            have hp0 : p0 = 0 := by
              have : (a0^2+a1^2+a2^2)*p0 = 0 := by rw [hpk0, ht, zero_mul]
              exact (mul_eq_zero.mp this).resolve_left hNA
            have hp1 : p1 = 0 := by
              have : (a0^2+a1^2+a2^2)*p1 = 0 := by rw [hpk1, ht, zero_mul]
              exact (mul_eq_zero.mp this).resolve_left hNA
            have hp2 : p2 = 0 := by
              have : (a0^2+a1^2+a2^2)*p2 = 0 := by rw [hpk2, ht, zero_mul]
              exact (mul_eq_zero.mp this).resolve_left hNA
            obtain ⟨z0, z1, z2⟩ := hZ ⟨hp0, hp1, hp2⟩
            have hb0 : (1 + (a0^2+a1^2+a2^2)) * b0 = 0 := by linear_combination (-1)*z0
            have hb1 : (1 + (a0^2+a1^2+a2^2)) * b1 = 0 := by linear_combination (-1)*z1
            have hb2 : (1 + (a0^2+a1^2+a2^2)) * b2 = 0 := by linear_combination (-1)*z2
            have hpos : (1 + (a0^2+a1^2+a2^2)) ≠ 0 := by positivity
            have hb0' := (mul_eq_zero.mp hb0).resolve_left hpos
            have hb1' := (mul_eq_zero.mp hb1).resolve_left hpos
            have hb2' := (mul_eq_zero.mp hb2).resolve_left hpos
            apply hNB
            rw [hb0', hb1', hb2']
            ring
      · exfalso
        have hfin : (a0^2+a1^2+a2^2)*(b0^2+b1^2+b2^2) = 0 := by
          linear_combination (-b0)*f0 - b1*f1 - b2*f2 + (a0*b0+a1*b1+a2*b2)*hAB
        rcases mul_eq_zero.mp hfin with h | h
        · exact hNA h
        · exact hNB h
    · have f0 : a1*(a0*b1-a1*b0) - a2*(a2*b0-a0*b2) = 0 :=
        (mul_eq_zero.mp (by linear_combination e0 :
          lam*(a1*(a0*b1-a1*b0) - a2*(a2*b0-a0*b2)) = 0)).resolve_left hlam
      have f1 : a2*(a1*b2-a2*b1) - a0*(a0*b1-a1*b0) = 0 :=
        (mul_eq_zero.mp (by linear_combination e1 :
          lam*(a2*(a1*b2-a2*b1) - a0*(a0*b1-a1*b0)) = 0)).resolve_left hlam
      have f2 : a0*(a2*b0-a0*b2) - a1*(a1*b2-a2*b1) = 0 :=
        (mul_eq_zero.mp (by linear_combination e2 :
          lam*(a0*(a2*b0-a0*b2) - a1*(a1*b2-a2*b1)) = 0)).resolve_left hlam
      have hfin : (a0^2+a1^2+a2^2) * ((a1*b2-a2*b1)^2 + (a2*b0-a0*b2)^2
          + (a0*b1-a1*b0)^2) = 0 := by
        linear_combination (a1*(a0*b1-a1*b0) - a2*(a2*b0-a0*b2))*f0
          + (a2*(a1*b2-a2*b1) - a0*(a0*b1-a1*b0))*f1
          + (a0*(a2*b0-a0*b2) - a1*(a1*b2-a2*b1))*f2
      rcases mul_eq_zero.mp hfin with h | h
      · exact hNA h
      · exact hNW h
  have key1 : ∀ e0 e1 e2 a0 a1 a2 b0 b1 b2 : ℝ,
      e1*a2 - e2*a1 = 0 → e2*a0 - e0*a2 = 0 → e0*a1 - e1*a0 = 0 →
      e1*b2 - e2*b1 = 0 → e2*b0 - e0*b2 = 0 → e0*b1 - e1*b0 = 0 →
      e0^2+e1^2+e2^2 ≠ 0 →
      (a1*b2 - a2*b1 = 0 ∧ a2*b0 - a0*b2 = 0 ∧ a0*b1 - a1*b0 = 0) := by
    intro e0 e1 e2 a0 a1 a2 b0 b1 b2 x1 x2 x3 y1 y2 y3 hN
    have hA0 : a0*(e0^2+e1^2+e2^2) = (e0*a0+e1*a1+e2*a2)*e0 := by
      linear_combination (-e1)*x3 + e2*x2
    have hA1 : a1*(e0^2+e1^2+e2^2) = (e0*a0+e1*a1+e2*a2)*e1 := by
      linear_combination e0*x3 - e2*x1
    have hA2 : a2*(e0^2+e1^2+e2^2) = (e0*a0+e1*a1+e2*a2)*e2 := by
      linear_combination (-e0)*x2 + e1*x1
    have hB0 : b0*(e0^2+e1^2+e2^2) = (e0*b0+e1*b1+e2*b2)*e0 := by
      linear_combination (-e1)*y3 + e2*y2
    have hB1 : b1*(e0^2+e1^2+e2^2) = (e0*b0+e1*b1+e2*b2)*e1 := by
      linear_combination e0*y3 - e2*y1
    have hB2 : b2*(e0^2+e1^2+e2^2) = (e0*b0+e1*b1+e2*b2)*e2 := by
      linear_combination (-e0)*y2 + e1*y1
    have hW0 : (e0^2+e1^2+e2^2)^2 * (a1*b2 - a2*b1) = 0 := by
      linear_combination ((e0^2+e1^2+e2^2)*b2)*hA1 + ((e0*a0+e1*a1+e2*a2)*e1)*hB2
        - ((e0^2+e1^2+e2^2)*b1)*hA2 - ((e0*a0+e1*a1+e2*a2)*e2)*hB1
    have hW1 : (e0^2+e1^2+e2^2)^2 * (a2*b0 - a0*b2) = 0 := by
      linear_combination ((e0^2+e1^2+e2^2)*b0)*hA2 + ((e0*a0+e1*a1+e2*a2)*e2)*hB0
        - ((e0^2+e1^2+e2^2)*b2)*hA0 - ((e0*a0+e1*a1+e2*a2)*e0)*hB2
    have hW2 : (e0^2+e1^2+e2^2)^2 * (a0*b1 - a1*b0) = 0 := by
      linear_combination ((e0^2+e1^2+e2^2)*b1)*hA0 + ((e0*a0+e1*a1+e2*a2)*e0)*hB1
        - ((e0^2+e1^2+e2^2)*b0)*hA1 - ((e0*a0+e1*a1+e2*a2)*e1)*hB0
    have hN2 : (e0^2+e1^2+e2^2)^2 ≠ 0 := pow_ne_zero 2 hN
    exact ⟨(mul_eq_zero.mp hW0).resolve_left hN2, (mul_eq_zero.mp hW1).resolve_left hN2,
      (mul_eq_zero.mp hW2).resolve_left hN2⟩
  have hA : i a ≠ 0 := by
    intro h0
    apply hW
    rw [h0]
    funext j
    fin_cases j <;> simp [hc0, hc1, hc2]
  have hB : i b ≠ 0 := by
    intro h0
    apply hW
    rw [h0]
    funext j
    fin_cases j <;> simp [hc0, hc1, hc2]
  have hab : i (a * b) = i a ⨯₃ i b := by
    rcases h a b with h1 | h1
    · exact h1.symm
    · exact absurd h1 hW
  have hNA := (hnz _ hA).ne'
  have hNB := (hnz _ hB).ne'
  have hNWe : (i a 1 * i b 2 - i a 2 * i b 1)^2 + (i a 2 * i b 0 - i a 0 * i b 2)^2
      + (i a 0 * i b 1 - i a 1 * i b 0)^2 ≠ 0 := by
    intro hz
    apply (hnz _ hW).ne'
    simp only [hc0, hc1, hc2]
    linear_combination hz
  by_cases hE : i 1 = 0
  · have hCne : i a⁻¹ ≠ 0 := by
      intro h0
      apply hA
      have ha : a⁻¹ = 1 := i.injective (h0.trans hE.symm)
      rw [inv_eq_one.mp ha]
      exact hE
    have hNC := (hnz _ hCne).ne'
    have hAC : i a ⨯₃ i a⁻¹ = 0 := by
      rcases h a a⁻¹ with h1 | h1
      · rw [mul_inv_cancel, hE] at h1
        exact h1
      · exact h1
    have hDa := h a⁻¹ (a * b)
    rw [hab, inv_mul_cancel_left] at hDa
    have hQ := h a (a * b)
    rw [hab] at hQ
    have hPB := h (a * a) b
    rw [mul_assoc] at hPB
    have hCP := h a⁻¹ (a * a)
    rw [inv_mul_cancel_left] at hCP
    have hZ : (i (a*a) 0 = 0 ∧ i (a*a) 1 = 0 ∧ i (a*a) 2 = 0) →
        (i (a*(a*b)) 0 = i b 0 ∧ i (a*(a*b)) 1 = i b 1 ∧ i (a*(a*b)) 2 = i b 2) := by
      rintro ⟨p0, p1, p2⟩
      have h0 : i (a*a) = 0 := (hext _ _).2 ⟨p0, p1, p2⟩
      have h1 : a*a = 1 := i.injective (h0.trans hE.symm)
      have h2 : a*(a*b) = b := by rw [← mul_assoc, h1, one_mul]
      rw [h2]
      exact ⟨rfl, rfl, rfl⟩
    obtain ⟨u0, u1, u2⟩ := (hext _ _).1 hAC
    simp only [hc0, hc1, hc2, Pi.zero_apply] at u0 u1 u2
    exact key0 (i a 0) (i a 1) (i a 2) (i b 0) (i b 1) (i b 2)
      (i a⁻¹ 0) (i a⁻¹ 1) (i a⁻¹ 2) (i (a*a) 0) (i (a*a) 1) (i (a*a) 2)
      (i (a*(a*b)) 0) (i (a*(a*b)) 1) (i (a*(a*b)) 2)
      (i a 1 * i b 2 - i a 2 * i b 1) (i a 2 * i b 0 - i a 0 * i b 2)
      (i a 0 * i b 1 - i a 1 * i b 0) rfl rfl rfl hNA hNB hNC hNWe
      (by linear_combination u0) (by linear_combination u1) (by linear_combination u2)
      (by
        rcases hDa with h1 | h1
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2] at v0 v1 v2
          exact Or.inl ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2, Pi.zero_apply] at v0 v1 v2
          exact Or.inr ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩)
      (by
        rcases hQ with h1 | h1
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2] at v0 v1 v2
          exact Or.inl ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2, Pi.zero_apply] at v0 v1 v2
          exact Or.inr ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩)
      (by
        rcases hPB with h1 | h1
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2] at v0 v1 v2
          exact Or.inl ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2, Pi.zero_apply] at v0 v1 v2
          exact Or.inr ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩)
      (by
        rcases hCP with h1 | h1
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2] at v0 v1 v2
          exact Or.inl ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩
        · obtain ⟨v0, v1, v2⟩ := (hext _ _).1 h1
          simp only [hc0, hc1, hc2, Pi.zero_apply] at v0 v1 v2
          exact Or.inr ⟨by linear_combination v0, by linear_combination v1,
            by linear_combination v2⟩)
      hZ
  · have EA : i 1 ⨯₃ i a = 0 := by
      rcases h 1 a with h1 | h1
      · rw [one_mul] at h1
        exfalso
        obtain ⟨u0, u1, u2⟩ := (hext _ _).1 h1
        simp only [hc0, hc1, hc2] at u0 u1 u2
        apply hNA
        linear_combination (-(i a 0)) * u0 - (i a 1) * u1 - (i a 2) * u2
      · exact h1
    have EB : i 1 ⨯₃ i b = 0 := by
      rcases h 1 b with h1 | h1
      · rw [one_mul] at h1
        exfalso
        obtain ⟨u0, u1, u2⟩ := (hext _ _).1 h1
        simp only [hc0, hc1, hc2] at u0 u1 u2
        apply hNB
        linear_combination (-(i b 0)) * u0 - (i b 1) * u1 - (i b 2) * u2
      · exact h1
    obtain ⟨u0, u1, u2⟩ := (hext _ _).1 EA
    simp only [hc0, hc1, hc2, Pi.zero_apply] at u0 u1 u2
    obtain ⟨y0, y1, y2⟩ := (hext _ _).1 EB
    simp only [hc0, hc1, hc2, Pi.zero_apply] at y0 y1 y2
    obtain ⟨w0, w1, w2⟩ := key1 (i 1 0) (i 1 1) (i 1 2) (i a 0) (i a 1) (i a 2)
      (i b 0) (i b 1) (i b 2) (by linear_combination u0) (by linear_combination u1)
      (by linear_combination u2) (by linear_combination y0) (by linear_combination y1)
      (by linear_combination y2) (hnz _ hE).ne'
    apply hW
    funext j
    fin_cases j <;> simp [hc0, hc1, hc2] <;> linarith
