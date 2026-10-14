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
  have cr0 : ∀ x y : Fin 3 → ℝ, (x ⨯₃ y) 0 = x 1 * y 2 - x 2 * y 1 := by
    intro x y; simp [cross_apply]
  have cr1 : ∀ x y : Fin 3 → ℝ, (x ⨯₃ y) 1 = x 2 * y 0 - x 0 * y 2 := by
    intro x y; simp [cross_apply]
  have cr2 : ∀ x y : Fin 3 → ℝ, (x ⨯₃ y) 2 = x 0 * y 1 - x 1 * y 0 := by
    intro x y; simp [cross_apply]
  have ext3 : ∀ x y : Fin 3 → ℝ, x 0 = y 0 → x 1 = y 1 → x 2 = y 2 → x = y := by
    intro x y h0 h1 h2; funext j; fin_cases j <;> simp [h0, h1, h2]
  have zero3 : ∀ x : Fin 3 → ℝ, x = 0 ↔ x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 := by
    intro x; constructor
    · rintro rfl; simp
    · rintro ⟨h0, h1, h2⟩; exact ext3 _ _ h0 h1 h2
  have sq0 : ∀ y : ℝ, y ^ 2 = 0 → y = 0 := fun y hy => (pow_eq_zero_iff two_ne_zero).mp hy
  have spos : ∀ x : Fin 3 → ℝ, x ≠ 0 → 0 < x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    intro x hx
    rcases (by positivity : (0:ℝ) ≤ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2).lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply hx; apply (zero3 x).mpr
      have q0 : x 0 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (x 1), sq_nonneg (x 2)]) (sq_nonneg _)
      have q1 : x 1 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (x 0), sq_nonneg (x 2)]) (sq_nonneg _)
      have q2 : x 2 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (x 0), sq_nonneg (x 1)]) (sq_nonneg _)
      exact ⟨sq0 _ q0, sq0 _ q1, sq0 _ q2⟩
  have hself : ∀ x y : Fin 3 → ℝ, x ⨯₃ y = y → y = 0 := by
    intro x y e
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    have e2 := congrFun e 2
    rw [cr0] at e0; rw [cr1] at e1; rw [cr2] at e2
    have hs : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 0 := by
      linear_combination (-y 0) * e0 + (-y 1) * e1 + (-y 2) * e2
    apply (zero3 y).mpr
    have q0 : y 0 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (y 1), sq_nonneg (y 2)]) (sq_nonneg _)
    have q1 : y 1 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (y 0), sq_nonneg (y 2)]) (sq_nonneg _)
    have q2 : y 2 ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg (y 0), sq_nonneg (y 1)]) (sq_nonneg _)
    exact ⟨sq0 _ q0, sq0 _ q1, sq0 _ q2⟩
  have anti : ∀ x y : Fin 3 → ℝ, x ⨯₃ y = 0 → y ⨯₃ x = 0 := by
    intro x y e
    obtain ⟨e0, e1, e2⟩ := (zero3 _).mp e
    apply (zero3 _).mpr
    simp only [cr0, cr1, cr2] at e0 e1 e2 ⊢
    exact ⟨by linear_combination -e0, by linear_combination -e1, by linear_combination -e2⟩
  have perp : ∀ u x : Fin 3 → ℝ, u ≠ 0 → u ⨯₃ x = 0 →
      ∃ l : ℝ, x 0 = l * u 0 ∧ x 1 = l * u 1 ∧ x 2 = l * u 2 := by
    intro u x hu hx
    have hs := spos u hu
    have hx0 := congrFun hx 0
    have hx1 := congrFun hx 1
    have hx2 := congrFun hx 2
    simp only [cr0, cr1, cr2, Pi.zero_apply] at hx0 hx1 hx2
    refine ⟨(u 0 * x 0 + u 1 * x 1 + u 2 * x 2) / (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2), ?_, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
      linear_combination (-u 1) * hx2 + u 2 * hx1
    · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
      linear_combination (-u 2) * hx0 + u 0 * hx2
    · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
      linear_combination (-u 0) * hx1 + u 1 * hx0
  have par : ∀ u x y : Fin 3 → ℝ, u ≠ 0 → u ⨯₃ x = 0 → u ⨯₃ y = 0 → x ⨯₃ y = 0 := by
    intro u x y hu hx hy
    obtain ⟨l, hl0, hl1, hl2⟩ := perp u x hu hx
    obtain ⟨m, hm0, hm1, hm2⟩ := perp u y hu hy
    apply (zero3 _).mpr
    simp only [cr0, cr1, cr2, hl0, hl1, hl2, hm0, hm1, hm2]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  by_contra hne
  have hab : i a ⨯₃ i b = i (a * b) := (h a b).resolve_right hne
  by_cases hu : i 1 = 0
  · have hA : i a ≠ 0 := fun e => hne (by rw [e]; simp)
    have hB : i b ≠ 0 := fun e => hne (by rw [e]; simp)
    have hinv : ∀ g : G, i g ⨯₃ i g⁻¹ = 0 := by
      intro g
      rcases h g g⁻¹ with e | e
      · rw [mul_inv_cancel, hu] at e; exact e
      · exact e
    obtain ⟨l, hl0, hl1, hl2⟩ := perp (i a) (i a⁻¹) hA (hinv a)
    have hXne : i a⁻¹ ≠ 0 := by
      intro e
      have h1 : a⁻¹ = 1 := i.injective (e.trans hu.symm)
      exact hA (by rw [inv_eq_one.mp h1, hu])
    have hl : l ≠ 0 := by
      rintro rfl
      apply hXne
      apply (zero3 _).mpr
      refine ⟨?_, ?_, ?_⟩
      · rw [hl0]; ring
      · rw [hl1]; ring
      · rw [hl2]; ring
    have hXB : i a⁻¹ ⨯₃ i b ≠ 0 := by
      intro e
      obtain ⟨f0, f1, f2⟩ := (zero3 _).mp e
      simp only [cr0, cr1, cr2, hl0, hl1, hl2] at f0 f1 f2
      apply hne
      apply (zero3 _).mpr
      simp only [cr0, cr1, cr2]
      refine ⟨?_, ?_, ?_⟩
      · exact (mul_eq_zero.mp (show l * ((i a) 1 * (i b) 2 - (i a) 2 * (i b) 1) = 0 by
          linear_combination f0)).resolve_left hl
      · exact (mul_eq_zero.mp (show l * ((i a) 2 * (i b) 0 - (i a) 0 * (i b) 2) = 0 by
          linear_combination f1)).resolve_left hl
      · exact (mul_eq_zero.mp (show l * ((i a) 0 * (i b) 1 - (i a) 1 * (i b) 0) = 0 by
          linear_combination f2)).resolve_left hl
    have hD : i a⁻¹ ⨯₃ i b = i (a⁻¹ * b) := (h a⁻¹ b).resolve_right hXB
    have hAD := h a (a⁻¹ * b)
    rw [← hD, mul_inv_cancel_left] at hAD
    have hAC := h a (a * b)
    rw [← hab] at hAC
    have hWB := h (a * a) b
    rw [mul_assoc] at hWB
    have hWX := h (a * a) a⁻¹
    rw [mul_inv_cancel_right] at hWX
    have hXA : i (a * a) = 0 → i a⁻¹ = i a := by
      intro e
      have h1 : a * a = 1 := i.injective (e.trans hu.symm)
      rw [inv_eq_of_mul_eq_one_right h1]
    set A := i a with hAd
    set B := i b with hBd
    set X := i a⁻¹ with hXd
    set W := i (a * a) with hWd
    set P := i (a * (a * b)) with hPd
    have hs : 0 < A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2 := spos A hA
    have hsB : 0 < B 0 ^ 2 + B 1 ^ 2 + B 2 ^ 2 := spos B hB
    -- A × C ≠ 0 (C = A × B)
    have hCne : A ⨯₃ (A ⨯₃ B) = 0 → False := by
      intro e
      have k0 := congrFun e 0
      have k1 := congrFun e 1
      have k2 := congrFun e 2
      simp only [cr0, cr1, cr2, Pi.zero_apply] at k0 k1 k2
      have c0 : (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * (A 1 * B 2 - A 2 * B 1) = 0 := by
        linear_combination (-A 1) * k2 + A 2 * k1
      have c1 : (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * (A 2 * B 0 - A 0 * B 2) = 0 := by
        linear_combination (-A 2) * k0 + A 0 * k2
      have c2 : (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * (A 0 * B 1 - A 1 * B 0) = 0 := by
        linear_combination (-A 0) * k1 + A 1 * k0
      apply hne
      apply (zero3 _).mpr
      simp only [cr0, cr1, cr2]
      exact ⟨(mul_eq_zero.mp c0).resolve_left hs.ne', (mul_eq_zero.mp c1).resolve_left hs.ne',
        (mul_eq_zero.mp c2).resolve_left hs.ne'⟩
    rcases hAD with e | e
    · -- A × D = B
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      have e2 := congrFun e 2
      simp only [cr0, cr1, cr2, hl0, hl1, hl2] at e0 e1 e2
      have g0 : (1 + l * (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2)) * (A 1 * B 2 - A 2 * B 1) = 0 := by
        linear_combination (-A 1) * e2 + A 2 * e1
      have g1 : (1 + l * (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2)) * (A 2 * B 0 - A 0 * B 2) = 0 := by
        linear_combination (-A 2) * e0 + A 0 * e2
      have g2 : (1 + l * (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2)) * (A 0 * B 1 - A 1 * B 0) = 0 := by
        linear_combination (-A 0) * e1 + A 1 * e0
      have hμ : 1 + l * (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) = 0 := by
        by_contra hμ
        apply hne
        apply (zero3 _).mpr
        simp only [cr0, cr1, cr2]
        exact ⟨(mul_eq_zero.mp g0).resolve_left hμ, (mul_eq_zero.mp g1).resolve_left hμ,
          (mul_eq_zero.mp g2).resolve_left hμ⟩
      have hAB : A 0 * B 0 + A 1 * B 1 + A 2 * B 2 = 0 := by
        linear_combination (-A 0) * e0 + (-A 1) * e1 + (-A 2) * e2
      rcases hAC with eC | eC
      swap
      · exact (hCne eC).elim
      have eP0 : P 0 = -(A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * B 0 := by
        rw [← eC]; simp only [cr0, cr1, cr2]; linear_combination A 0 * hAB
      have eP1 : P 1 = -(A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * B 1 := by
        rw [← eC]; simp only [cr0, cr1, cr2]; linear_combination A 1 * hAB
      have eP2 : P 2 = -(A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * B 2 := by
        rw [← eC]; simp only [cr0, cr1, cr2]; linear_combination A 2 * hAB
      rcases hWB with f | f
      · have f0 := congrFun f 0
        have f1 := congrFun f 1
        have f2 := congrFun f 2
        rw [eP0] at f0; rw [eP1] at f1; rw [eP2] at f2
        simp only [cr0, cr1, cr2] at f0 f1 f2
        have hk : (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) * (B 0 ^ 2 + B 1 ^ 2 + B 2 ^ 2) = 0 := by
          linear_combination B 0 * f0 + B 1 * f1 + B 2 * f2
        exact absurd hk (mul_pos hs hsB).ne'
      · obtain ⟨t, ht0, ht1, ht2⟩ := perp B W hB (anti _ _ f)
        rcases hWX with g | g
        · have g0 := congrFun g 0
          have g1 := congrFun g 1
          have g2 := congrFun g 2
          simp only [cr0, cr1, cr2, ht0, ht1, ht2, hl0, hl1, hl2] at g0 g1 g2
          have hk : A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2 = 0 := by
            linear_combination (-A 0) * g0 + (-A 1) * g1 + (-A 2) * g2
          exact absurd hk hs.ne'
        · have g0 := congrFun g 0
          have g1 := congrFun g 1
          have g2 := congrFun g 2
          simp only [cr0, cr1, cr2, ht0, ht1, ht2, hl0, hl1, hl2, Pi.zero_apply] at g0 g1 g2
          have htl : t * l = 0 := by
            by_contra htl
            apply hne
            apply (zero3 _).mpr
            simp only [cr0, cr1, cr2]
            refine ⟨?_, ?_, ?_⟩
            · exact (mul_eq_zero.mp (show (t * l) * (A 1 * B 2 - A 2 * B 1) = 0 by
                linear_combination (-1 : ℝ) * g0)).resolve_left htl
            · exact (mul_eq_zero.mp (show (t * l) * (A 2 * B 0 - A 0 * B 2) = 0 by
                linear_combination (-1 : ℝ) * g1)).resolve_left htl
            · exact (mul_eq_zero.mp (show (t * l) * (A 0 * B 1 - A 1 * B 0) = 0 by
                linear_combination (-1 : ℝ) * g2)).resolve_left htl
          have ht : t = 0 := (mul_eq_zero.mp htl).resolve_right hl
          have hW0 : W = 0 := (zero3 W).mpr ⟨by rw [ht0, ht]; ring, by rw [ht1, ht]; ring,
            by rw [ht2, ht]; ring⟩
          have hXA' : X = A := hXA hW0
          rw [hXA'] at hl0 hl1 hl2
          have hsl : A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2 = l * (A 0 ^ 2 + A 1 ^ 2 + A 2 ^ 2) := by
            linear_combination A 0 * hl0 + A 1 * hl1 + A 2 * hl2
          linarith [hμ, hsl, hs]
    · -- A × D = 0 ⇒ A × C = 0
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      have e2 := congrFun e 2
      simp only [cr0, cr1, cr2, hl0, hl1, hl2, Pi.zero_apply] at e0 e1 e2
      apply hCne
      apply (zero3 _).mpr
      refine ⟨?_, ?_, ?_⟩
      · have h' : l * (A ⨯₃ (A ⨯₃ B)) 0 = 0 := by
          simp only [cr0, cr1, cr2]; linear_combination e0
        exact (mul_eq_zero.mp h').resolve_left hl
      · have h' : l * (A ⨯₃ (A ⨯₃ B)) 1 = 0 := by
          simp only [cr0, cr1, cr2]; linear_combination e1
        exact (mul_eq_zero.mp h').resolve_left hl
      · have h' : l * (A ⨯₃ (A ⨯₃ B)) 2 = 0 := by
          simp only [cr0, cr1, cr2]; linear_combination e2
        exact (mul_eq_zero.mp h').resolve_left hl
  · have k1 : i 1 ⨯₃ i a = 0 := by
      rcases h 1 a with e | e
      · rw [one_mul] at e
        exact absurd (hself _ _ e) (fun h0 => hne (by rw [h0]; simp))
      · exact e
    have k2 : i 1 ⨯₃ i b = 0 := by
      rcases h 1 b with e | e
      · rw [one_mul] at e
        exact absurd (hself _ _ e) (fun h0 => hne (by rw [h0]; simp))
      · exact e
    exact hne (par _ _ _ hu k1 k2)
