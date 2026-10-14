import Mathlib

open Polynomial

/--
Show that $\mathbb{Z}[X]/(x^2+4)$ is not integrally closed.
-/
theorem not_isIntegrallyClosed_adjoinRoot_pow_two_add_four :
    ¬ IsIntegrallyClosed (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) := by
  set f : ℤ[X] := X ^ 2 + C 4 with hfdef
  have hf : f.Monic := by
    rw [hfdef]; exact monic_X_pow_add (by compute_degree!)
  have hf1 : f ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hfdef] at this
    simp [natDegree_add_eq_left_of_natDegree_lt] at this
  have hfdeg : f.natDegree = 2 := by
    rw [hfdef]; compute_degree!
  -- normal form
  have key : ∀ r : AdjoinRoot f, ∃ a b : ℤ, r = (a : AdjoinRoot f) * AdjoinRoot.root f + (b : AdjoinRoot f) := by
    intro r
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
    have hp : AdjoinRoot.mk f p = AdjoinRoot.mk f (p %ₘ f) := by
      conv_lhs => rw [← modByMonic_add_div p f]
      simp [AdjoinRoot.mk_self]
    have hdeg : (p %ₘ f).natDegree ≤ 1 := by
      have := natDegree_modByMonic_lt p hf hf1
      rw [hfdeg] at this; omega
    refine ⟨(p %ₘ f).coeff 1, (p %ₘ f).coeff 0, ?_⟩
    rw [hp]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
    simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, eq_intCast, Int.cast_id]
    simp [AdjoinRoot.of, algebraMap_int_eq, eq_intCast]
  -- the embedding into ℂ
  have hfx : eval₂ (Int.castRingHom ℂ) (2 * Complex.I) f = 0 := by
    rw [hfdef]
    simp <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num
  let ψ : AdjoinRoot f →+* ℂ := AdjoinRoot.lift (Int.castRingHom ℂ) (2 * Complex.I) hfx
  have ψx : ψ (AdjoinRoot.root f) = 2 * Complex.I := AdjoinRoot.lift_root hfx
  have ψnat : ∀ a b : ℤ, ψ ((a : AdjoinRoot f) * AdjoinRoot.root f + (b : AdjoinRoot f))
      = (2 * a * Complex.I + b : ℂ) := by
    intro a b
    simp [map_add, map_mul, ψx]
    ring
  have ψ2 : ψ 2 = 2 := map_ofNat ψ 2
  have ψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨a, b, rfl⟩ := key r
    rw [ψnat] at hr
    have h1 := congrArg Complex.re hr
    have h2 := congrArg Complex.im hr
    simp at h1 h2
    have hb : b = 0 := by exact_mod_cast h1
    have ha : a = 0 := by exact_mod_cast h2
    subst ha; subst hb; simp
  have : IsDomain (AdjoinRoot f) := ψinj.isDomain ψ
  intro hI
  let K := FractionRing (AdjoinRoot f)
  let x : AdjoinRoot f := AdjoinRoot.root f
  have hx : x ^ 2 + 4 = 0 := by
    have := AdjoinRoot.mk_self (f := f)
    rw [hfdef] at this
    simp [map_add, map_pow, AdjoinRoot.mk_X, x] at this ⊢
    exact this
  have hinj := IsFractionRing.injective (AdjoinRoot f) K
  have h2ne : (algebraMap (AdjoinRoot f) K) 2 ≠ 0 := by
    intro h
    have h' : (2 : AdjoinRoot f) = 0 := hinj (by rw [h, map_zero])
    have : ψ 2 = ψ 0 := by rw [h']
    rw [ψ2, map_zero] at this
    norm_num at this
  have h4ne : (4 : K) ≠ 0 := by
    have h4R : (4 : AdjoinRoot f) ≠ 0 := by
      intro h
      have : ψ 4 = ψ 0 := by rw [h]
      rw [map_ofNat ψ 4, map_zero] at this
      norm_num at this
    have := (map_ne_zero_iff (algebraMap (AdjoinRoot f) K) hinj).mpr h4R
    rwa [map_ofNat] at this
  obtain ⟨y, hydef⟩ : ∃ y : K, y * algebraMap (AdjoinRoot f) K 2 = algebraMap (AdjoinRoot f) K x :=
    ⟨algebraMap (AdjoinRoot f) K x / algebraMap (AdjoinRoot f) K 2, div_mul_cancel₀ _ h2ne⟩
  have hy' : y * 2 = algebraMap (AdjoinRoot f) K x := by
    rw [← hydef, map_ofNat]
  have hxK' : (algebraMap (AdjoinRoot f) K x) ^ 2 + 4 = 0 := by
    have := congrArg (algebraMap (AdjoinRoot f) K) hx
    rw [map_add, map_pow, map_ofNat, map_zero] at this
    exact this
  have hyint : IsIntegral (AdjoinRoot f) y := by
    refine ⟨X ^ 2 + C 1, ?_, ?_⟩
    · exact monic_X_pow_add (by compute_degree!)
    · have hy2 : (4 : K) * (y ^ 2 + 1) = 0 := by
        linear_combination (y * 2 + algebraMap (AdjoinRoot f) K x) * hy' + hxK'
      have := (mul_eq_zero.mp hy2).resolve_left h4ne
      simpa [eval₂_add, eval₂_pow, eval₂_X, eval₂_C] using this
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyint
  have hzx : z * 2 = x := by
    apply hinj
    rw [map_mul, map_ofNat, hz]
    exact hy'
  have hψ : ψ z = Complex.I := by
    have := congrArg ψ hzx
    rw [map_mul, ψx, ψ2] at this
    have : (2 : ℂ) * (ψ z - Complex.I) = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    · linear_combination h
  obtain ⟨a, b, hab⟩ := key z
  rw [hab, ψnat] at hψ
  have h2 : (2 * a : ℝ) = 1 := by
    have := congrArg Complex.im hψ
    simpa using this
  have : (2 * a : ℤ) = 1 := by exact_mod_cast h2
  omega
