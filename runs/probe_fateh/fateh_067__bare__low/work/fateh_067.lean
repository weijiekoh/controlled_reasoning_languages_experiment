import Mathlib

open Polynomial

/--
Prove that the prime ideals of $\mathbb{F}_7[\alpha] \otimes_{\mathbb{F}_7} \mathbb{F}_7[\alpha]$ are principal, where $\alpha^3 = 2$.
-/
theorem isPrincipal_of_ideal_tensor_zMod_seven
    (p : Ideal (TensorProduct (ZMod 7) (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7)))
    (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))))) [p.IsPrime] : p.IsPrincipal := by
  have h7 : ∀ a : ZMod 7, a ^ 3 - 2 ≠ 0 := by decide
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hirr : Irreducible (X ^ 3 - 2 : Polynomial (ZMod 7)) := by
    have hm : (X ^ 3 - 2 : Polynomial (ZMod 7)).natDegree = 3 := by compute_degree!
    refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (p := (X ^ 3 - 2 : Polynomial (ZMod 7))) (by omega) (by omega)).2 ?_
    rw [Multiset.eq_zero_iff_forall_notMem]
    intro a ha
    rw [mem_roots (by intro h; rw [h] at hm; simp at hm)] at ha
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_ofNat] at ha
    exact h7 a ha
  haveI : Fact (Irreducible (X ^ 3 - 2 : Polynomial (ZMod 7))) := ⟨hirr⟩
  letI : Field (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))) := AdjoinRoot.instField
  let φ : (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7)))[X] →+* TensorProduct (ZMod 7) (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))) (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))) :=
    eval₂RingHom (Algebra.TensorProduct.includeLeftRingHom) (1 ⊗ₜ AdjoinRoot.root _)
  have key : ∀ g : Polynomial (ZMod 7), ∃ u, φ u = (1 : (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7)))) ⊗ₜ[ZMod 7] AdjoinRoot.mk _ g := by
    intro g
    induction g using Polynomial.induction_on with
    | C c =>
      refine ⟨C (algebraMap _ (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))) c), ?_⟩
      simp [φ]
      exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := ZMod 7) (A := AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))) c
    | add f g hf hg =>
      obtain ⟨u, hu⟩ := hf
      obtain ⟨v, hv⟩ := hg
      exact ⟨u + v, by rw [map_add, hu, hv, map_add, TensorProduct.tmul_add]⟩
    | monomial n c h =>
      obtain ⟨u, hu⟩ := h
      refine ⟨u * X, ?_⟩
      rw [map_mul, hu]
      simp [φ, pow_succ, ← mul_assoc]
  have hs : Function.Surjective φ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective b
      obtain ⟨u, hu⟩ := key g
      refine ⟨C a * u, ?_⟩
      rw [map_mul, hu]
      simp [φ]
    | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add _ _ _⟩
  rw [← Ideal.map_comap_of_surjective φ hs p]
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (Ideal.comap φ p)).principal
  rw [hg, Ideal.map_span, Set.image_singleton]
  exact ⟨⟨φ g, rfl⟩⟩
