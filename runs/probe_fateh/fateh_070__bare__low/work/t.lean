import Mathlib

open Polynomial

/--
Show that $\mathbb{Z}[X]/(x^2+4)$ is not integrally closed.
-/
theorem not_isIntegrallyClosed_adjoinRoot_pow_two_add_four :
    ¬ IsIntegrallyClosed (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) := by
  intro h
  set f : ℤ[X] := X ^ 2 + C 4 with hfdef
  have hm : f.Monic := by
    rw [hfdef]; exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hd : f.natDegree = 2 := by
    rw [hfdef]; exact Polynomial.natDegree_X_pow_add_C
  have hroot : (AdjoinRoot.root f)^2 + 4 = 0 := by
    have := AdjoinRoot.eval₂_root f
    simpa [hfdef] using this
  have h2 : (2 : AdjoinRoot f) ∈ nonZeroDivisors (AdjoinRoot f) := by
    rw [mem_nonZeroDivisors_iff]
    suffices key : ∀ a : AdjoinRoot f, 2 * a = 0 → a = 0 from ⟨key, fun a ha => key a (by rwa [mul_comm])⟩
    intro a ha
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
    have : AdjoinRoot.mk f (C 2 * p) = 0 := by
      simpa using ha
    rw [AdjoinRoot.mk_eq_zero] at this
    rw [AdjoinRoot.mk_eq_zero]
    have e := Polynomial.modByMonic_add_div p hm
    have hdv : f ∣ C 2 * (p %ₘ f) := by
      have : C 2 * p = C 2 * (p %ₘ f) + f * (C 2 * (p /ₘ f)) := by
        conv_lhs => rw [← e]
        ring
      rw [this] at *
      exact (dvd_add_left (dvd_mul_right _ _)).mp ‹_›
    have hlt : (p %ₘ f).degree < f.degree := Polynomial.degree_modByMonic_lt _ hm
    have hz : C 2 * (p %ₘ f) = 0 := by
      apply Polynomial.eq_zero_of_dvd_of_degree_lt hdv
      calc (C 2 * (p %ₘ f)).degree ≤ (p %ₘ f).degree := Polynomial.degree_C_mul_le _ _ 
        _ < _ := hlt
    have hr : p %ₘ f = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · simp at h
      · exact h
    rw [← e, hr]; simp
  have hinj := IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))
  set K := FractionRing (AdjoinRoot f)
  set z : K := IsLocalization.mk' K (AdjoinRoot.root f) (⟨2, h2⟩ : nonZeroDivisors (AdjoinRoot f)) with hz
  have hspec : z * algebraMap _ K 2 = algebraMap _ K (AdjoinRoot.root f) := by
    have := IsLocalization.mk'_spec K (AdjoinRoot.root f) (⟨2, h2⟩ : nonZeroDivisors (AdjoinRoot f))
    exact this
  have hu : IsUnit (algebraMap (AdjoinRoot f) K 2) :=
    IsLocalization.map_units K (⟨2, h2⟩ : nonZeroDivisors (AdjoinRoot f))
  have hint : IsIntegral (AdjoinRoot f) z := by
    refine ⟨X ^ 2 + 1, by simpa using Polynomial.monic_X_pow_add_C (1 : AdjoinRoot f) (n := 2) (by norm_num), ?_⟩
    have h4 : (z ^ 2 + 1) * (algebraMap _ K 2) ^ 2 = 0 := by
      have : (z ^ 2 + 1) * (algebraMap _ K 2) ^ 2 = algebraMap _ K ((AdjoinRoot.root f)^2 + 4) := by
        simp only [map_add, map_pow, ← hspec, map_ofNat]
        ring
      rw [this, hroot]; simp
    have := (hu.pow 2).mul_left_eq_zero.mp h4
    simpa [Polynomial.eval₂_add] using this
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have : r * 2 = AdjoinRoot.root f := by
    apply hinj
    rw [map_mul, hr, hspec]; simp
  let φ : AdjoinRoot f →+* DualNumber (ZMod 2) :=
    AdjoinRoot.lift (Int.castRingHom _) (DualNumber.eps) (by
      simp [hfdef])
  have := congrArg φ this
  simp at this
  have h2z : (2 : DualNumber (ZMod 2)) = 0 := CharTwo.two_eq_zero
  rw [map_ofNat, h2z] at this
  simp [φ] at this
