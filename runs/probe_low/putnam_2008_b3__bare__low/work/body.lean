  have nsq : ∀ (u v : EuclideanSpace ℝ (Fin 4)), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 → ∀ a b : ℝ,
      ‖a • u + b • v‖^2 = a^2 + b^2 := by
    intro u v hu hv h a b
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, h, hu, hv]
    simp [sq_abs]
  subst H_def
  constructor
  · rw [contains_def]
    set u : EuclideanSpace ℝ (Fin 4) := !₂[1/2,1/2,1/2,1/2] with hu
    set v : EuclideanSpace ℝ (Fin 4) := !₂[1/2,-1/2,1/2,-1/2] with hv
    have hu1 : ‖u‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]; simp [hu, Fin.sum_univ_four]; norm_num
    have hv1 : ‖v‖ = 1 := by
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]; simp [hv, Fin.sum_univ_four]; norm_num
    have huv : inner ℝ u v = 0 := by
      simp [hu, hv, inner, Fin.sum_univ_four]; norm_num
    have hli : LinearIndependent ℝ ![u, v] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (fun x => inner ℝ u x) hst
      have h2 := congrArg (fun x => inner ℝ v x) hst
      simp only [inner_add_right, inner_smul_right, inner_zero_right, huv, real_inner_self_eq_norm_sq, hu1, hv1,
        real_inner_comm u v] at h1 h2
      constructor <;> nlinarith
    refine ⟨AffineSubspace.mk' 0 (Submodule.span ℝ {u, v}), 0, ?_, ?_, ?_⟩
    · simp
    · rw [AffineSubspace.direction_mk']
      have := finrank_span_eq_card hli
      simpa using this
    · intro P ⟨hP1, hP2⟩
      have hP2' : P ∈ Submodule.span ℝ {u, v} := by simpa using hP2
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hP2'
      rw [← hab] at hP1 ⊢
      have hn := nsq u v hu1 hv1 huv a b
      have : ‖a • u + b • v‖ = Real.sqrt 2 / 2 := by simpa using hP1
      rw [this] at hn
      have h2 : (Real.sqrt 2 / 2)^2 = 1/2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      rw [h2] at hn
      intro i
      fin_cases i <;> simp [hu, hv, abs_le] <;> constructor <;> nlinarith [sq_nonneg (a-b), sq_nonneg (a+b)]
  · intro r hr
    rw [contains_def] at hr
    obtain ⟨A, C, hC, hdim, hsub⟩ := hr
    by_cases hr0 : r ≤ 0
    · have : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
      linarith
    push_neg at hr0
    let b0 := (stdOrthonormalBasis ℝ A.direction).reindex (finCongr hdim)
    set u : EuclideanSpace ℝ (Fin 4) := (b0 0 : EuclideanSpace ℝ (Fin 4)) with hu
    set v : EuclideanSpace ℝ (Fin 4) := (b0 1 : EuclideanSpace ℝ (Fin 4)) with hv
    have hu1 : ‖u‖ = 1 := by simpa [hu] using b0.orthonormal.1 0
    have hv1 : ‖v‖ = 1 := by simpa [hv] using b0.orthonormal.1 1
    have huv : inner ℝ u v = 0 := by
      have := b0.orthonormal.2 (show (0:Fin 2) ≠ 1 by decide)
      simpa [hu, hv] using this
    have hum : u ∈ A.direction := (b0 0).2
    have hvm : v ∈ A.direction := (b0 1).2
    have key : ∀ i : Fin 4, ∀ a b : ℝ, a^2 + b^2 = 1 → r * (a * u i + b * v i) ≤ 1/2 := by
      intro i a b hab
      have hmem : ∀ s : ℝ, s = 1 ∨ s = -1 → C + (s*r*a) • u + (s*r*b) • v ∈ sphere C r ∩ (A : Set _) := by
        intro s hs
        have hs2 : s^2 = 1 := by rcases hs with h | h <;> simp [h]
        constructor
        · rw [mem_sphere, dist_eq_norm]
          have : C + (s*r*a) • u + (s*r*b) • v - C = (s*r*a) • u + (s*r*b) • v := by abel
          rw [this]
          have hn := nsq u v hu1 hv1 huv (s*r*a) (s*r*b)
          have : (s*r*a)^2 + (s*r*b)^2 = r^2 := by
            calc _ = s^2*r^2*(a^2+b^2) := by ring
              _ = _ := by rw [hab, hs2]; ring
          rw [this] at hn
          nlinarith [norm_nonneg ((s*r*a) • u + (s*r*b) • v)]
        · have h1 := A.vadd_mem_of_mem_direction (A.direction.add_mem (A.direction.smul_mem (s*r*a) hum) (A.direction.smul_mem (s*r*b) hvm)) hC
          simpa [vadd_eq_add, add_assoc, add_comm] using h1
      have h1 := hsub (hmem 1 (Or.inl rfl)) i
      have h2 := hsub (hmem (-1) (Or.inr rfl)) i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_le] at h1 h2
      nlinarith [h1.2, h2.1]
    have hcoord : ∀ i : Fin 4, r^2 * (u i ^2 + v i ^2) ≤ 1/4 := by
      intro i
      by_cases hs : u i ^2 + v i ^2 = 0
      · rw [hs]; norm_num
      have hpos : 0 < u i ^2 + v i ^2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
      set s := Real.sqrt (u i ^2 + v i ^2) with hsd
      have hs2 : s^2 = u i ^2 + v i ^2 := Real.sq_sqrt hpos.le
      have hspos : 0 < s := Real.sqrt_pos.mpr hpos
      have := key i (u i / s) (v i / s) (by field_simp; linarith)
      have e : u i / s * u i + v i / s * v i = s := by
        field_simp; linarith
      rw [e] at this
      nlinarith
    have hsum : ∑ i : Fin 4, (u i ^2 + v i ^2) = 2 := by
      have h1 := hu1; have h2 := hv1
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1 h2
      simp only [Real.norm_eq_abs, sq_abs] at h1 h2
      rw [Finset.sum_add_distrib]; linarith
    have : 2 * r^2 ≤ 1 := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcoord i)
      rw [← Finset.mul_sum, hsum] at this
      simp at this; linarith
    have h2 : (Real.sqrt 2 / 2)^2 = 1/2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have : (0:ℝ) ≤ Real.sqrt 2 / 2 := by positivity
    nlinarith
