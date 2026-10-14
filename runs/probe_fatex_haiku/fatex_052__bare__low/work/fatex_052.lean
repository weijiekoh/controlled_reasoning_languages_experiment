import Mathlib

namespace Problem52

/--
Let $R$ be a ring, \( \mathfrak{m} \) is an ideal in the Jacobson radical of \( R \),
and \( G_{1}, G_{2} \in R[x] \) are polynomials such that $G_1$ is monic.
If $G_i \mod \mathfrak{m}$ gnerate the unit ideal of $R/\mathfrak{m}[x]$,
then \( G_{1}, G_{2} \) together generate the unit ideal of \( R[x] \).
-/
theorem generate_unit_ideal_of_quotient (R : Type) [CommRing R] (m : Ideal R)
    (h_le_jac : m ≤ Ring.jacobson R) (G₁ G₂ : Polynomial R) (h_monic : G₁.Monic)
    (h_gen : Ideal.span {G₁.map (Ideal.Quotient.mk m), G₂.map (Ideal.Quotient.mk m)} = ⊤) :
    Ideal.span {G₁, G₂} = ⊤ := by
  classical
  set I : Ideal (Polynomial R) := Ideal.span {G₁, G₂} with hI
  set W : Submodule R (Polynomial R) := I.restrictScalars R with hW
  -- key: every polynomial differs from an element of I by coefficients in m
  have key : ∀ p : Polynomial R, ∃ w ∈ I, ∀ k, (p - w).coeff k ∈ m := by
    intro p
    have hp : p.map (Ideal.Quotient.mk m) ∈
        Ideal.span {G₁.map (Ideal.Quotient.mk m), G₂.map (Ideal.Quotient.mk m)} := by
      rw [h_gen]; exact Submodule.mem_top
    obtain ⟨c, d, hcd⟩ := Ideal.mem_span_pair.1 hp
    obtain ⟨c', rfl⟩ := Polynomial.map_surjective _ (Ideal.Quotient.mk_surjective) c
    obtain ⟨d', rfl⟩ := Polynomial.map_surjective _ (Ideal.Quotient.mk_surjective) d
    refine ⟨c' * G₁ + d' * G₂, ?_, ?_⟩
    · exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · intro k
      have h0 : (p - (c' * G₁ + d' * G₂)).map (Ideal.Quotient.mk m) = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
          hcd]
        ring
      have := congrArg (fun q => Polynomial.coeff q k) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at this
      exact (Ideal.Quotient.eq_zero_iff_mem).1 this
  set Q := Polynomial R ⧸ W with hQ
  set n := G₁.natDegree with hn
  have hfin : Module.Finite R Q := by
    rw [Module.finite_def]
    refine ⟨(Finset.range (n + 1)).image (fun i => W.mkQ (Polynomial.X ^ i)), ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨p, rfl⟩ := W.mkQ_surjective q
    have hdiv := Polynomial.modByMonic_add_div p G₁
    have hm : G₁ * (p /ₘ G₁) ∈ W := by
      show G₁ * (p /ₘ G₁) ∈ I
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have h0 : W.mkQ (G₁ * (p /ₘ G₁)) = 0 := by
      rw [W.mkQ_apply]; exact (Submodule.Quotient.mk_eq_zero W).2 hm
    have hpr : W.mkQ p = W.mkQ (p %ₘ G₁) := by
      conv_lhs => rw [← hdiv]
      rw [map_add, h0, add_zero]
    have hle : (p %ₘ G₁).natDegree ≤ n := by
      by_cases h : G₁ = 1
      · rw [h, Polynomial.modByMonic_one]; simp
      · exact (Polynomial.natDegree_modByMonic_lt p h_monic h).le
    have hr : W.mkQ (p %ₘ G₁) = ∑ i ∈ Finset.range ((p %ₘ G₁).natDegree + 1),
        (p %ₘ G₁).coeff i • W.mkQ (Polynomial.X ^ i) := by
      conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow (p %ₘ G₁)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Polynomial.smul_eq_C_mul, map_smul]
    rw [hpr, hr]
    refine Submodule.sum_mem _ fun i hi => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨i, Finset.mem_range.2 ?_, rfl⟩
    have := Finset.mem_range.1 hi
    omega
  have hsub : (⊤ : Submodule R Q) ≤ m • (⊤ : Submodule R Q) := by
    intro q _
    obtain ⟨p, rfl⟩ := W.mkQ_surjective q
    obtain ⟨w, hwI, hw⟩ := key p
    have hwW : w ∈ W := hwI
    have hq : W.mkQ (p - w) = W.mkQ p := by
      rw [map_sub, W.mkQ_apply w, (Submodule.Quotient.mk_eq_zero W).2 hwW, sub_zero]
    have hg : p - w = ∑ i ∈ Finset.range ((p - w).natDegree + 1),
        (p - w).coeff i • (Polynomial.X : Polynomial R) ^ i := by
      conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow (p - w)]
      simp [Polynomial.smul_eq_C_mul]
    rw [← hq, hg, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hw i) Submodule.mem_top
  have hbot : (⊤ : Submodule R Q) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m ⊤ (Module.finite_def.1 hfin) hsub
      (by rwa [Ideal.jacobson_bot])
  have h1 : (1 : Polynomial R) ∈ I := by
    have h1' : W.mkQ (1 : Polynomial R) ∈ (⊤ : Submodule R Q) := Submodule.mem_top
    rw [hbot, Submodule.mem_bot, W.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1'
    exact h1'
  exact (Ideal.eq_top_iff_one _).2 h1

end Problem52
