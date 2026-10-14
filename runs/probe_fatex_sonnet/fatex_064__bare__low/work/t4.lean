import Mathlib
open CategoryTheory Abelian

theorem L2 {R F : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    (hinj : Function.Injective (algebraMap R F)) (m : Ideal R) [m.IsPrime]
    (x : F) (a : R) (ha : a ∈ m) (ha0 : a ≠ 0)
    (h1 : ∀ y ∈ m, ∃ z : R, algebraMap R F z = x * algebraMap R F y)
    (h2 : ¬ ∃ q u : R, u ∉ m ∧ algebraMap R F q = x * algebraMap R F u) :
    ∃ φ : (IsLocalRing.maximalIdeal (Localization.AtPrime m)) →ₗ[Localization.AtPrime m] Localization.AtPrime m,
      ∀ ψ : Localization.AtPrime m →ₗ[Localization.AtPrime m] Localization.AtPrime m, ¬ (∀ y : IsLocalRing.maximalIdeal (Localization.AtPrime m), ψ y = φ y) := by
  classical
  set A := Localization.AtPrime m with hA
  have hu : ∀ y : m.primeCompl, IsUnit (algebraMap R F y) := by
    intro y
    refine IsUnit.mk0 _ ?_
    intro h0
    have : (y:R) = 0 := hinj (by rw [h0, map_zero])
    exact y.2 (this ▸ m.zero_mem)
  let g : A →+* F := IsLocalization.lift (M := m.primeCompl) hu
  have hg : ∀ r : R, g (algebraMap R A r) = algebraMap R F r := fun r => IsLocalization.lift_eq hu r
  let : Algebra A F := g.toAlgebra
  have hgi : Function.Injective g := by
    rw [IsLocalization.lift_injective_iff]
    intro r s
    constructor
    · intro h; rw [← hg, ← hg, h]
    · intro h; exact congrArg _ (hinj h)
  have hsm : ∀ y : A, y • x = g y * x := fun y => rfl
  have hmk : ∀ (q : R) (u : m.primeCompl), g (IsLocalization.mk' A q u) * algebraMap R F u = algebraMap R F q := by
    intro q u
    rw [← hg, ← hg, ← map_mul, IsLocalization.mk'_spec]
  have hne : ∀ u : m.primeCompl, algebraMap R F u ≠ 0 := fun u => (hu u).ne_zero
  have key : ∀ y ∈ IsLocalRing.maximalIdeal A, ∃ w : A, g w = g y * x := by
    intro y hy
    obtain ⟨⟨q, u⟩, rfl⟩ := IsLocalization.mk'_surjective m.primeCompl y
    beta_reduce at hy
    have hq : q ∈ m := (IsLocalization.AtPrime.mk'_mem_maximal_iff A m q u).1 hy
    obtain ⟨z, hz⟩ := h1 q hq
    refine ⟨IsLocalization.mk' A z u, ?_⟩
    apply mul_right_cancel₀ (hne u)
    beta_reduce
    rw [hmk, hz]
    show _ = g (IsLocalization.mk' A q u) * x * _
    rw [mul_right_comm, hmk, mul_comm]
  let θ : A →ₗ[A] F := LinearMap.toSpanSingleton A F x
  let θ' : IsLocalRing.maximalIdeal A →ₗ[A] LinearMap.range (Algebra.linearMap A F) :=
    LinearMap.codRestrict _ (θ.comp (Submodule.subtype _)) (by
      intro y
      obtain ⟨w, hw⟩ := key y.1 y.2
      refine ⟨w, ?_⟩
      show g w = g y * x
      exact hw)
  let e := LinearEquiv.ofInjective (Algebra.linearMap A F) hgi
  let φ := e.symm.toLinearMap.comp θ'
  have hφ : ∀ y : IsLocalRing.maximalIdeal A, g (φ y) = g y * x := by
    intro y
    have : e (φ y) = θ' y := by simp [φ]
    have := congrArg Subtype.val this
    exact this
  refine ⟨φ, ?_⟩
  intro ψ hψ
  have ha' : algebraMap R A a ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A m a _).2 ha
  have h3 := hψ ⟨algebraMap R A a, ha'⟩
  have h4 : ψ (algebraMap R A a) = algebraMap R A a * ψ 1 := by
    have := ψ.map_smul (algebraMap R A a) 1
    simpa using this
  have h5 := hφ ⟨algebraMap R A a, ha'⟩
  simp only [← h3] at h5
  rw [h4, map_mul, hg] at h5
  have hane : algebraMap R F a ≠ 0 := fun h0 => ha0 (hinj (by rw [h0, map_zero]))
  have h6 : g (ψ 1) = x := by
    apply mul_left_cancel₀ hane
    rw [h5]
  obtain ⟨⟨q, u⟩, hqu⟩ := IsLocalization.mk'_surjective m.primeCompl (ψ 1)
  have h7 := hmk q u
  beta_reduce at hqu
  rw [← hqu] at h6
  apply h2
  refine ⟨q, u, u.2, ?_⟩
  rw [← h7]
  beta_reduce at h6
  rw [h6]
