import Mathlib

/--
Let $n$ be a positive integer. Suppose that $A$, $B$, and $M$ are $n \times n$ matrices with real entries such that $AM = MB$, and such that $A$ and $B$ have the same characteristic polynomial. Prove that $\det(A-MX)=\det(B-XM)$ for every $n \times n$ matrix $X$ with real entries.
-/
theorem putnam_2015_a6
(n : ℕ)
(A B M : Matrix (Fin n) (Fin n) ℝ)
(npos : n > 0)
(hmul : A * M = M * B)
(hpoly : Matrix.charpoly A = Matrix.charpoly B)
: ∀ X : Matrix (Fin n) (Fin n) ℝ, (A - M * X).det = (B - X * M).det := by
  intro X
  have evC : ∀ N : Matrix (Fin n) (Fin n) ℝ, ∀ s : ℝ,
      (Matrix.charpoly N).eval s = (s • 1 - N).det := by
    intro N s
    unfold Matrix.charpoly
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.charmatrix, Matrix.one_apply, Matrix.scalar_apply, h]
  have evP : ∀ N : Matrix (Fin n) (Fin n) ℝ, ∀ s : ℝ,
      (((Polynomial.X : Polynomial ℝ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) -
        N.map Polynomial.C).det).eval s = (s • 1 - N).det := by
    intro N s
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  -- key identity at points where the charpoly is nonzero
  have key : ∀ s : ℝ, (Matrix.charpoly A).eval s ≠ 0 →
      (s • 1 - (A - M * X)).det = (s • 1 - (B - X * M)).det := by
    intro s hs
    have hdetS : (s • 1 - A).det ≠ 0 := by rw [← evC]; exact hs
    have hdetT : (s • 1 - B).det = (s • 1 - A).det := by
      rw [← evC, ← evC, hpoly]
    have hSu : IsUnit (s • 1 - A).det := isUnit_iff_ne_zero.mpr hdetS
    have hTu : IsUnit (s • 1 - B).det := by rw [hdetT]; exact hSu
    have hSM : (s • 1 - A) * M = M * (s • 1 - B) := by
      simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, hmul]
    have e : (s • 1 - A)⁻¹ * M * (s • 1 - B) = M := by
      rw [Matrix.mul_assoc, ← hSM, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul]
    have h1 : (s • 1 - A)⁻¹ * M = M * (s • 1 - B)⁻¹ := by
      calc (s • 1 - A)⁻¹ * M
          = (s • 1 - A)⁻¹ * M * ((s • 1 - B) * (s • 1 - B)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hTu, Matrix.mul_one]
        _ = ((s • 1 - A)⁻¹ * M * (s • 1 - B)) * (s • 1 - B)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = M * (s • 1 - B)⁻¹ := by rw [e]
    have hfixS : (s • 1 - A) * ((s • 1 - A)⁻¹ * M * X) = M * X := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul]
    have hfixT : (s • 1 - B) * ((s • 1 - B)⁻¹ * X * M) = X * M := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTu, Matrix.one_mul]
    have hL : (s • 1 - A) + M * X = (s • 1 - A) * (1 + (s • 1 - A)⁻¹ * M * X) := by
      rw [Matrix.mul_add, Matrix.mul_one, hfixS]
    have hR : (s • 1 - B) + X * M = (s • 1 - B) * (1 + (s • 1 - B)⁻¹ * X * M) := by
      rw [Matrix.mul_add, Matrix.mul_one, hfixT]
    have e1 : s • 1 - (A - M * X) = (s • 1 - A) + M * X := by abel
    have e2 : s • 1 - (B - X * M) = (s • 1 - B) + X * M := by abel
    have h2 : (s • 1 - A)⁻¹ * M * X = M * ((s • 1 - B)⁻¹ * X) := by
      rw [h1, Matrix.mul_assoc]
    have hsyl : (1 + (s • 1 - A)⁻¹ * M * X).det = (1 + (s • 1 - B)⁻¹ * X * M).det := by
      rw [h2, Matrix.det_one_add_mul_comm, Matrix.mul_assoc]
    rw [e1, e2, hL, hR, Matrix.det_mul, Matrix.det_mul, hsyl, hdetT]
  have hcp0 : Matrix.charpoly A ≠ 0 := (Matrix.charpoly_monic A).ne_zero
  have hinf : Set.Infinite {x : ℝ | ¬ (Matrix.charpoly A).eval x = 0} :=
    (Polynomial.finite_setOf_isRoot hcp0).infinite_compl
  have hPQ : (((Polynomial.X : Polynomial ℝ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) -
        (A - M * X).map Polynomial.C).det) -
      (((Polynomial.X : Polynomial ℝ) • (1 : Matrix (Fin n) (Fin n) (Polynomial ℝ)) -
        (B - X * M).map Polynomial.C).det) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ hinf
    intro s hs
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub] at hs ⊢
    rw [evP, evP, sub_eq_zero]
    exact key s hs
  have h0 := congrArg (Polynomial.eval 0) hPQ
  simp only [Polynomial.eval_sub, Polynomial.eval_zero] at h0
  rw [evP, evP] at h0
  have h0' : (-1 : ℝ) ^ n * (A - M * X).det = (-1) ^ n * (B - X * M).det := by
    simp only [zero_smul, zero_sub, Matrix.det_neg, sub_eq_zero, Fintype.card_fin] at h0
    exact h0
  exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h0'
