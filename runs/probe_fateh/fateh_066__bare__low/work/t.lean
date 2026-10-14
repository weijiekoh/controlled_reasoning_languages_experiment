import Mathlib
open Polynomial
theorem X1 {n : ℕ} (hn : n ≥ 3) :
    ¬ Irreducible (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X]) := by
  intro hf
  set f : (ZMod 2)[X] := X ^ 2 ^ n + X + C 1 with hfdef
  have : Fact (Irreducible f) := ⟨hf⟩
  have hdeg : f.natDegree = 2 ^ n := by
    rw [hfdef]; rw [add_assoc]
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
    have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    calc (X + C 1 : (ZMod 2)[X]).natDegree ≤ 1 := by
          apply natDegree_add_le_of_degree_le <;> simp
      _ < _ := this
  let K := AdjoinRoot f
  have : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  let r : K := AdjoinRoot.root f
  have hr : r ^ 2 ^ n = r + 1 := by
    have h : aeval r f = 0 := AdjoinRoot.aeval_eq _ |>.trans (by simp [AdjoinRoot.mk_self])
    have h' : r ^ 2 ^ n + (r + 1) = 0 := by simpa [hfdef, add_assoc] using h
    exact CharTwo.add_eq_zero.mp h'
  have hr2 : r ^ 2 ^ (2*n) = r := by
    have : (2:ℕ)^(2*n) = 2^n * 2^n := by rw [two_mul, pow_add]
    rw [this, pow_mul, hr, add_pow_char_pow, hr]
    have : (1:K)^(2^n) = 1 := one_pow _
    rw [this, add_assoc]
    have : (1:K) + 1 = 0 := by
      have := CharTwo.add_self_eq_zero (1:K); exact this
    rw [this, add_zero]
  let ψ : K →+* K := iterateFrobenius K 2 (2*n)
  let ψa : K →ₐ[ZMod 2] K :=
    { toRingHom := ψ
      commutes' := fun c => by
        exact congrFun (congrArg DFunLike.coe (Subsingleton.elim (ψ.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))) c }
  have hall : ∀ x : K, x ^ 2 ^ (2*n) = x := by
    have : ψa = AlgHom.id _ _ := by
      apply AdjoinRoot.algHom_ext
      exact hr2
    intro x
    have := congrArg (fun g => g x) this
    exact this
  have : Module.Finite (ZMod 2) K := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have : Finite K := Module.finite_of_finite (ZMod 2)
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ 2 ^ n := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [this, ZMod.card, (AdjoinRoot.powerBasis hf.ne_zero).finrank]
    simp [AdjoinRoot.powerBasis_dim, hdeg]
  have hnd : (X ^ 2 ^ (2*n) - X : K[X]).natDegree = 2 ^ (2*n) := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp
    omega
  have hne : (X ^ 2 ^ (2*n) - X : K[X]) ≠ 0 := by
    intro h
    rw [h] at hnd
    simp at hnd
    exact absurd hnd.symm (by positivity)
  have hle := Polynomial.card_le_degree_of_subset_roots (p := (X ^ 2 ^ (2*n) - X : K[X])) (Z := Finset.univ) (by
    intro x _
    rw [mem_roots hne]
    simp [hall x])
  rw [hnd] at hle
  simp [hcard] at hle
  have h1 : ∀ m, 3 ≤ m → 2 * m < 2 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have h2 := h1 n hn
  have : 2 ^ (2*n) < 2 ^ 2 ^ n := Nat.pow_lt_pow_right (by norm_num) h2
  omega
