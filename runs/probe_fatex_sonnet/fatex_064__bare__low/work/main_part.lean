theorem main_aux (k : Type) [Field k] :
    ¬ IsCohenMacaulayRing (Algebra.adjoin k (S0 k)) := by
  intro hCM
  classical
  let P := MvPolynomial (Fin 2) k
  let R := Algebra.adjoin k (S0 k)
  let c : ↥R →+* k := (constantCoeff (σ := Fin 2) (R := k)).comp (R.val : ↥R →+* P)
  let m : Ideal ↥R := RingHom.ker c
  haveI : m.IsPrime := RingHom.ker_isPrime c
  have hinj : Function.Injective (algebraMap ↥R (FractionRing P)) := by
    intro r s h
    apply Subtype.ext
    apply IsFractionRing.injective P (FractionRing P)
    exact h
  have g1 : (X 0 ^ 4 : P) ∈ R := Algebra.subset_adjoin (by simp [S0])
  have g2 : (X 0 ^ 3 * X 1 : P) ∈ R := Algebra.subset_adjoin (by simp [S0])
  let xP : P := X 0 ^ 2 * X 1 ^ 2
  let a : ↥R := ⟨X 0 ^ 4, g1⟩
  let b : ↥R := ⟨X 0 ^ 3 * X 1, g2⟩
  have ha : a ∈ m := by
    show c a = 0
    simp [c, a]
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg Subtype.val h
    simp [a] at this
  have h1 : ∀ y ∈ m, ∃ z : ↥R, algebraMap ↥R (FractionRing P) z = algebraMap P (FractionRing P) xP * algebraMap ↥R (FractionRing P) y := by
    intro y hy
    have hy0 : constantCoeff (y : P) = 0 := hy
    have := Qmem k y.1 y.2
    rw [hy0] at this
    simp only [map_zero, sub_zero] at this
    refine ⟨⟨xP * y, this⟩, ?_⟩
    show algebraMap P (FractionRing P) (xP * y) = _
    rw [map_mul]; rfl
  have h2 : ¬ ∃ q u : ↥R, u ∉ m ∧ algebraMap ↥R (FractionRing P) q = algebraMap P (FractionRing P) xP * algebraMap ↥R (FractionRing P) u := by
    rintro ⟨q, u, hu, hqu⟩
    have : (q : P) = xP * u := by
      apply IsFractionRing.injective P (FractionRing P)
      rw [map_mul]; exact hqu
    have hc := Qsupp k q.1 q.2 (Finsupp.single 0 2 + Finsupp.single 1 2)
    have e : coeff (Finsupp.single 0 2 + Finsupp.single 1 2) (q : P) = constantCoeff (u : P) := by
      rw [this]
      have : xP = monomial (Finsupp.single 0 2 + Finsupp.single 1 2) (1:k) := by
        simp only [xP]
        rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
      rw [this]
      have := coeff_monomial_mul (σ := Fin 2) 0 (Finsupp.single 0 2 + Finsupp.single 1 2) (1 : k) (u : P)
      rw [add_zero] at this
      rw [this, one_mul]; rfl
    have hu0 : constantCoeff (u : P) ≠ 0 := hu
    rw [e] at hc
    rcases hc hu0 with h | h
    · have := congrArg (fun f => f 0) h
      simp at this
    · simp at h
  obtain ⟨φ, hφ⟩ := L2 hinj m (algebraMap P (FractionRing P) xP) a ha ha0 h1 h2
  have hnot := L1 (A := Localization.AtPrime m) (IsLocalRing.maximalIdeal (Localization.AtPrime m)) φ hφ
  -- the height-one prime
  let ρ : P →ₐ[k] Polynomial k := MvPolynomial.aeval ![Polynomial.X, 0]
  let ρ0 : ↥R →+* Polynomial k := (ρ : P →+* Polynomial k).comp (R.val : ↥R →+* P)
  let p : Ideal ↥R := RingHom.ker ρ0
  haveI : p.IsPrime := RingHom.ker_isPrime ρ0
  have hcomp : ∀ y : P, Polynomial.eval 0 (ρ y) = constantCoeff y := fun y => rho_comp k y
  have hpm : p < m := by
    rw [lt_iff_le_and_ne]
    constructor
    · intro y hy
      have hy' : ρ y.1 = 0 := hy
      show constantCoeff y.1 = 0
      rw [← hcomp, hy']; simp
    · intro h
      have : a ∈ p := h ▸ ha
      have h' : ρ (X 0 ^ 4) = 0 := this
      exact rho_a k h'
  have hp0 : p ≠ ⊥ := by
    intro h
    have : b ∈ p := by
      have hb : ρ (X 0 ^ 3 * X 1) = 0 := rho_b k
      exact hb
    rw [h] at this
    have := congrArg Subtype.val ((Submodule.mem_bot _).1 this)
    simp [b] at this
  have hdim := L3 m p hp0 hpm
  have hCM' := hCM.CM_localize m inferInstance
  have heq := hCM'.depth_eq_dim
  have hle : IsLocalRing.depth (R := Localization.AtPrime m) (ModuleCat.of (Localization.AtPrime m) (Localization.AtPrime m)) ≤ 1 := by
    unfold IsLocalRing.depth Ideal.depth moduleDepth
    apply sSup_le
    intro n hn
    by_contra hlt
    rw [not_le] at hlt
    apply hnot
    exact hn 1 (by exact_mod_cast hlt)
  rw [heq] at hdim
  have h2' : (2 : ℕ∞) ≤ IsLocalRing.depth (R := Localization.AtPrime m) (ModuleCat.of (Localization.AtPrime m) (Localization.AtPrime m)) :=
    WithBot.coe_le_coe.1 hdim
  have := h2'.trans hle
  exact absurd this (by decide)
