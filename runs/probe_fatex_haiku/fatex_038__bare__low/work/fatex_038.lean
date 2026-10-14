import Mathlib

namespace Problem38

open Polynomial DualNumber

/--
Let \( k \) be a field, and let \( R = k[t]/(t^2) \). Set
\[
p(x) = tx^3 + tx^2 - x^2 - x \in R[x].
\]
Let \( S = R[x]/(p) \).
-/
abbrev S (k : Type) [Field k] : Type := ((DualNumber k)[X] ⧸ Ideal.span {((C ε) * X^3 + (C ε) * X^2 - X^2 - X : (DualNumber k)[X])})

/--
\(S\) has a \(R\) module structure inherited from R[x].
-/
noncomputable instance (k : Type) [Field k] : Module (DualNumber k) (S k) := Module.compHom _ C

/--
Let \( k \) be a field, and let \( R = k[t]/(t^2) \). Set
\[
p(x) = tx^3 + tx^2 - x^2 - x \in R[x].
\]
Show that \( S = R[x]/(p) \) is a free \( R \)-module of rank \( 2 \).
-/
theorem free_dualNumber_and_rank_eq_2 (k : Type) [Field k] :
    Module.Free (DualNumber k) (S k) ∧ Module.rank (DualNumber k) (S k) = 2 := by
  classical
  have G : ∀ (R : Type) [CommRing R] (I J : Ideal R[X]) (h : I = J),
      ∃ f : (R[X] ⧸ I) ≃ₐ[R] (R[X] ⧸ J), ∀ (c : R) (x : R[X] ⧸ I),
        f ((C c) • x) = algebraMap R (R[X] ⧸ J) c • f x := by
    intro R _ I J h
    have : I.IsTwoSided := ⟨fun b ha => Ideal.mul_mem_right _ _ ha⟩
    have : J.IsTwoSided := ⟨fun b ha => Ideal.mul_mem_right _ _ ha⟩
    refine ⟨Ideal.quotientEquivAlgOfEq R h, fun c x => ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hc : algebraMap R[X] (R[X] ⧸ I) (C c) = algebraMap R (R[X] ⧸ I) c :=
      (IsScalarTower.algebraMap_apply R R[X] (R[X] ⧸ I) c).symm
    rw [show (C c) • (Ideal.Quotient.mk I) y = algebraMap R[X] (R[X] ⧸ I) (C c) * Ideal.Quotient.mk I y from rfl,
      map_mul, hc, AlgEquiv.commutes]
    rfl
  have hm : (X^2 + X : (DualNumber k)[X]).Monic := by monicity!
  have hu : IsUnit (C (ε : DualNumber k) * X - 1) := by
    refine isUnit_iff_exists.2 ⟨-(1 + C (ε : DualNumber k) * X), ?_, ?_⟩
    all_goals
      have h2 : C (ε : DualNumber k) * C ε = 0 := by rw [← C_mul, eps_mul_eps, C_0]
      linear_combination (-(X : (DualNumber k)[X])^2) * h2
  have hI : Ideal.span {(C (ε : DualNumber k) * X^3 + C ε * X^2 - X^2 - X : (DualNumber k)[X])}
      = Ideal.span {(X^2 + X : (DualNumber k)[X])} := by
    have : (C (ε : DualNumber k) * X^3 + C ε * X^2 - X^2 - X : (DualNumber k)[X])
        = (C (ε : DualNumber k) * X - 1) * (X^2 + X) := by ring
    rw [this, Ideal.span_singleton_mul_left_unit hu]
  obtain ⟨e, he⟩ := G (DualNumber k) _ _ hI
  let L : S k ≃ₗ[DualNumber k] AdjoinRoot (X^2 + X : (DualNumber k)[X]) :=
    { toFun := e
      invFun := e.symm
      map_add' := fun x y => e.map_add x y
      map_smul' := fun c x => by
        show e (C c • x) = c • e x
        rw [he c x]
        exact (Algebra.smul_def c (e x)).symm ▸ rfl
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }
  have hfree : Module.Free (DualNumber k) (AdjoinRoot (X^2 + X : (DualNumber k)[X])) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hm).basis
  have hdeg : (X^2 + X : (DualNumber k)[X]).natDegree = 2 := by compute_degree!
  refine ⟨Module.Free.of_equiv L.symm, ?_⟩
  rw [LinearEquiv.rank_eq L, rank_eq_card_basis (AdjoinRoot.powerBasis' hm).basis]
  simp [hdeg]

end Problem38
