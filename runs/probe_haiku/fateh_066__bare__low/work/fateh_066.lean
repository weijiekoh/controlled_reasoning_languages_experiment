import Mathlib

open Polynomial
/--
Prove that, if $n \geq 3$, then $x^{2^n}+x+1$ is \emph{reducible} in $\mathbb{F}_2$.
-/
theorem not_irreducible_X_pow_two_pow_add_X_add_C_one {n : ℕ} (hn : n ≥ 3) :
    ¬ Irreducible (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X]) := by
  intro hirr
  obtain ⟨f, hfdef⟩ : ∃ f : (ZMod 2)[X], f = X ^ 2 ^ n + X + C 1 := ⟨_, rfl⟩
  rw [← hfdef] at hirr
  have hdeg : f.natDegree = 2 ^ n := by
    have h1 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    rw [hfdef, natDegree_add_C, natDegree_add_eq_left_of_natDegree_lt] <;>
      simp [natDegree_X] <;> omega
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    have : 0 < 2 ^ n := by positivity
    omega
  have key0 : ∀ m : ℕ, 3 ≤ m → 2 * m < 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih => rw [pow_succ]; omega
  have sq : ∀ r : ZMod 2, r ^ 2 = r := by decide
  have hpow0 : ∀ r : ZMod 2, ∀ k : ℕ, r ^ (2 ^ k) = r := by
    intro r k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul, ih, sq]
  have := Fact.mk hirr
  have h2 : (2 : AdjoinRoot f) = 0 := by
    have h : ((2 : ZMod 2)) = 0 := rfl
    rw [← map_ofNat (algebraMap (ZMod 2) (AdjoinRoot f)) 2, h, map_zero]
  haveI : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_algebraMap (A := AdjoinRoot f) (algebraMap (ZMod 2) (AdjoinRoot f)).injective 2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ExpChar (AdjoinRoot f) 2 := ExpChar.prime Nat.prime_two
  have hx : (AdjoinRoot.root f) ^ 2 ^ n = AdjoinRoot.root f + 1 := by
    have h0 : AdjoinRoot.mk f (X ^ 2 ^ n + X + C 1) = 0 := by
      rw [← hfdef]; exact AdjoinRoot.mk_self
    simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h0
    linear_combination h0 - (AdjoinRoot.root f + 1) * h2
  have hfrob_root : (AdjoinRoot.root f) ^ (2 ^ (2 * n)) = AdjoinRoot.root f := by
    have e : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add]; congr 1; omega
    rw [e, pow_mul, hx]
    have : (AdjoinRoot.root f + 1) ^ 2 ^ n = (AdjoinRoot.root f) ^ 2 ^ n + 1 := by
      rw [add_pow_char_pow]; simp
    rw [this, hx]
    linear_combination h2
  haveI : Module.Finite (ZMod 2) (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 2)
  haveI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot f) = 2 ^ (2 ^ n) := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := AdjoinRoot f)
    rw [this, ZMod.card, (AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  let Frob : AdjoinRoot f →ₐ[ZMod 2] AdjoinRoot f :=
    { (iterateFrobenius (AdjoinRoot f) 2 (2 * n)) with
      commutes' := by
        intro a
        show (iterateFrobenius (AdjoinRoot f) 2 (2 * n)) (algebraMap (ZMod 2) (AdjoinRoot f) a) = _
        rw [iterateFrobenius_def, ← map_pow, hpow0] }
  have hall : ∀ y : AdjoinRoot f, y ^ (2 ^ (2 * n)) = y := by
    intro y
    have he := AdjoinRoot.algHom_ext (f := f) (g₁ := Frob) (g₂ := AlgHom.id (ZMod 2) (AdjoinRoot f)) (by
      show (iterateFrobenius (AdjoinRoot f) 2 (2 * n)) _ = _
      rw [iterateFrobenius_def]
      exact hfrob_root)
    have := congrArg (fun φ : AdjoinRoot f →ₐ[ZMod 2] AdjoinRoot f => φ y) he
    simp only [Frob, AlgHom.coe_mk, RingHom.coe_mk, iterateFrobenius_def, AlgHom.id_apply] at this
    exact this
  have hX : (X ^ (2 ^ (2 * n)) - X : (AdjoinRoot f)[X]) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_zero, natDegree_sub_eq_left_of_natDegree_lt] at this
    · rw [natDegree_X_pow] at this
      have : 0 < 2 ^ (2 * n) := by positivity
      omega
    · rw [natDegree_X_pow, natDegree_X]
      have : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
      omega
  have hsub : (Finset.univ : Finset (AdjoinRoot f)).val ⊆ (X ^ (2 ^ (2 * n)) - X : (AdjoinRoot f)[X]).roots := by
    intro y _
    rw [mem_roots hX]
    simp [IsRoot, hall]
  have hle := card_le_degree_of_subset_roots hsub
  rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow] at hle
  · rw [Finset.card_univ, hcard] at hle
    have key : 2 * n < 2 ^ n := key0 n hn
    have : 2 ^ (2 * n) < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by norm_num) key
    omega
  · rw [natDegree_X_pow, natDegree_X]
    have : 1 < 2 ^ (2 * n) := Nat.one_lt_two_pow (by omega)
    omega
