import Mathlib

namespace Problem64

section

open CategoryTheory Abelian Problem64

variable {R : Type} [CommRing R]

instance : CategoryTheory.HasExt.{0} (ModuleCat.{0} R) :=
  CategoryTheory.hasExt_of_enoughProjectives (ModuleCat R)

noncomputable def moduleDepth (N M : ModuleCat.{0} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (CategoryTheory.Abelian.Ext.{0} N M i)}

noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{0} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (R ⧸ I)) M

noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{0} R) : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

variable (R)

class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

end

open MvPolynomial

section aux
open CategoryTheory Abelian

theorem L1 {A : Type} [CommRing A] (I : Ideal A) (φ : I →ₗ[A] A)
    (h : ∀ ψ : A →ₗ[A] A, ¬ (∀ y : I, ψ y = φ y)) :
    ¬ Subsingleton (Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) 1) := by
  intro hs
  let S : ShortComplex (ModuleCat.{0} A) :=
    ShortComplex.mk (ModuleCat.ofHom (I.subtype)) (ModuleCat.ofHom (Submodule.mkQ I))
      (by ext x; exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    have : Mono S.f := (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype I)
    have : Epi S.g := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective I)
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, (Ideal.Quotient.eq_zero_iff_mem.1 hx)⟩, rfl⟩
  have ex := Ext.contravariant_sequence_exact₁' hS (ModuleCat.of A A) 0 1 (by simp)
  rw [ShortComplex.ab_exact_iff_ker_le_range] at ex
  have key := @ex (Ext.mk₀ (ModuleCat.ofHom φ)) (by
    rw [AddMonoidHom.mem_ker]; exact Subsingleton.elim _ _)
  obtain ⟨y, hy⟩ := key
  obtain ⟨g0, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  have hy2 : Ext.mk₀ (S.f ≫ g0) = Ext.mk₀ (ModuleCat.ofHom φ) := by
    rw [← Ext.mk₀_comp_mk₀]; exact hy
  have hy3 := (Ext.mk₀_bijective _ _).1 hy2
  apply h g0.hom
  intro z
  have := congrArg (fun e => e.hom z) hy3
  simpa [S] using this

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
  rw [h6]

theorem L3 {R : Type} [CommRing R] [IsDomain R] (m p : Ideal R) [m.IsPrime] [p.IsPrime]
    (h0 : p ≠ ⊥) (h1 : p < m) : (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime m) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  have hp : ¬ p.height ≤ (0:ℕ) := by
    rw [Ideal.height_le_iff]
    intro h
    have := h ⊥ Ideal.isPrime_bot (bot_lt_iff_ne_bot.2 h0)
    simp at this
  have hm : ¬ m.height ≤ (1:ℕ) := by
    rw [Ideal.height_le_iff]
    intro h
    have := h p inferInstance h1
    apply hp
    have : p.height < 1 := by simpa using this
    exact Order.lt_one_iff_nonpos.1 this |>.trans (le_refl _) 
  have : (2:ℕ∞) ≤ m.height := by
    by_contra hc
    rw [not_le] at hc
    apply hm
    generalize m.height = h at hc ⊢
    induction h using ENat.recTopCoe with
    | top => simp at hc
    | coe n =>
      have : n < 2 := by exact_mod_cast hc
      exact_mod_cast (by omega : n ≤ 1)
  exact WithBot.coe_le_coe.2 this
end aux

abbrev S0 (k : Type) [Field k] : Set (MvPolynomial (Fin 2) k) := {(X 0) ^ 4, (X 0) ^ 3 * X 1,
      X 0 * (X 1) ^ 3, (X 1) ^ 4}

theorem Qmem (k : Type) [Field k] (y : MvPolynomial (Fin 2) k) (hy : y ∈ Algebra.adjoin k (S0 k)) :
    ((X 0 : MvPolynomial (Fin 2) k) ^ 2 * X 1 ^ 2) * (y - C (constantCoeff y)) ∈ Algebra.adjoin k (S0 k) := by
  have g1 : (X 0 ^ 4 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  have g2 : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  have g3 : (X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  have g4 : (X 1 ^ 4 : MvPolynomial (Fin 2) k) ∈ Algebra.adjoin k (S0 k) := Algebra.subset_adjoin (by simp [S0])
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    simp only [S0, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · have := mul_mem g2 g2
      convert this using 1
      simp; ring
    · have := mul_mem g1 g3
      convert this using 1
      simp; ring
    · have := mul_mem g2 g4
      convert this using 1
      simp; ring
    · have := mul_mem g3 g3
      convert this using 1
      simp; ring
  | algebraMap c =>
    simp [MvPolynomial.algebraMap_eq]
  | add y z hy hz ihy ihz =>
    have := add_mem ihy ihz
    convert this using 1
    simp only [map_add, C_add]; ring
  | mul y z hy hz ihy ihz =>
    have := add_mem (mul_mem ihy hz) (mul_mem (Subalgebra.algebraMap_mem _ (constantCoeff y)) ihz)
    convert this using 1
    simp only [map_mul, C_mul, MvPolynomial.algebraMap_eq]; ring

theorem Qsupp (k : Type) [Field k] (y : MvPolynomial (Fin 2) k) (hy : y ∈ Algebra.adjoin k (S0 k)) :
    ∀ d, coeff d y ≠ 0 → d = 0 ∨ (4 ≤ d 0 + d 1 ∧ (d 0 + d 1) % 4 = 0 ∧
      d ≠ Finsupp.single 0 2 + Finsupp.single 1 2) := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    intro d hd
    right
    simp only [S0, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have e1 : (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) k) = monomial (Finsupp.single 0 3 + Finsupp.single 1 1) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul, one_mul]
    have e2 : (X 0 * X 1 ^ 3 : MvPolynomial (Fin 2) k) = monomial (Finsupp.single 0 1 + Finsupp.single 1 3) 1 := by
      rw [X_pow_eq_monomial, X, monomial_mul, one_mul]
    rcases hy with rfl | rfl | rfl | rfl
    · rw [X_pow_eq_monomial, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
    · rw [e1, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
    · rw [e2, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
    · rw [X_pow_eq_monomial, coeff_monomial] at hd
      split_ifs at hd with h
      · subst h; refine ⟨by simp, by simp, fun h2 => ?_⟩; have := congrArg (fun f => f 0) h2; simp at this
      · exact absurd rfl hd
  | algebraMap c =>
    intro d hd
    left
    rw [MvPolynomial.algebraMap_eq, coeff_C] at hd
    split_ifs at hd with h
    · exact h.symm
    · exact absurd rfl hd
  | add y z hy hz ihy ihz =>
    intro d hd
    rw [coeff_add] at hd
    by_cases h : coeff d y = 0
    · rw [h, zero_add] at hd; exact ihz d hd
    · exact ihy d h
  | mul y z hy hz ihy ihz =>
    intro d hd
    rw [coeff_mul] at hd
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : coeff x.1 y ≠ 0 := left_ne_zero_of_mul hne
    have h2 : coeff x.2 z ≠ 0 := right_ne_zero_of_mul hne
    subst hx
    rcases ihy _ h1 with h | h
    · rw [h, zero_add]; exact ihz _ h2
    · rcases ihz _ h2 with h' | h'
      · rw [h', add_zero]; exact Or.inr h
      · right
        obtain ⟨a1, a2, a3⟩ := h
        obtain ⟨b1, b2, b3⟩ := h'
        simp only [Finsupp.add_apply]
        refine ⟨by omega, by omega, ?_⟩
        intro h5
        have := congrArg (fun f => f 0 + f 1) h5
        simp at this
        omega

theorem rho_comp (k : Type) [Field k] (y : MvPolynomial (Fin 2) k) :
    Polynomial.eval 0 (aeval (R := k) (S₁ := Polynomial k) ![Polynomial.X, 0] y) = constantCoeff y := by
  have : (Polynomial.evalRingHom 0).comp ((aeval (R := k) (S₁ := Polynomial k) ![Polynomial.X, 0] : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k) : MvPolynomial (Fin 2) k →+* Polynomial k) = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro i; fin_cases i <;> simp
  exact congrArg (fun f => f y) this

theorem rho_a (k : Type) [Field k] :
    aeval (R := k) (S₁ := Polynomial k) ![Polynomial.X, 0] (X 0 ^ 4 : MvPolynomial (Fin 2) k) ≠ 0 := by
  simp

theorem rho_b (k : Type) [Field k] :
    aeval (R := k) (S₁ := Polynomial k) ![Polynomial.X, 0] (X 0 ^ 3 * X 1 : MvPolynomial (Fin 2) k) = 0 := by
  simp

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
