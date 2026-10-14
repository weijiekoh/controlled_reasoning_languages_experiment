import Mathlib

open Polynomial TensorProduct

noncomputable section

namespace Fate67
abbrev f7 : Polynomial (ZMod 7) := X ^ 3 - 2
instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem irr7 : Irreducible f7 := by
  have hm : f7.Monic := by unfold f7; monicity!
  have hd : f7.natDegree = 3 := by unfold f7; compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have h0 : f7 ≠ 0 := hm.ne_zero
  rw [mem_roots h0, IsRoot, f7] at hx
  simp at hx
  revert x
  decide

instance : Fact (Irreducible f7) := ⟨irr7⟩

abbrev A := AdjoinRoot f7
abbrev S := A × (A × A)

theorem hd3 : f7.natDegree = 3 := by unfold f7; compute_degree!

instance finA' : Module.Finite (ZMod 7) A := Module.Finite.of_basis (AdjoinRoot.powerBasis irr7.ne_zero).basis

theorem finA : Module.finrank (ZMod 7) A = 3 := by
  rw [(AdjoinRoot.powerBasis irr7.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hd3]

theorem finS : Module.finrank (ZMod 7) S = 9 := by
  rw [Module.finrank_prod, Module.finrank_prod, finA]

theorem finT : Module.finrank (ZMod 7) (TensorProduct (ZMod 7) A A) = 9 := by
  rw [Module.finrank_tensorProduct, finA]

def α : A := AdjoinRoot.root f7

theorem hα : α ^ 3 = 2 := by
  have := AdjoinRoot.eval₂_root f7
  simp [f7] at this
  unfold α
  linear_combination this

def D : A →ₐ[ZMod 7] S := (AlgHom.id (ZMod 7) A).prod ((AlgHom.id (ZMod 7) A).prod (AlgHom.id (ZMod 7) A))

def xv : S := (α, (2 * α, 4 * α))

theorem h7 : (7 : A) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 7) A) 7, show (OfNat.ofNat 7 : ZMod 7) = 0 from rfl, map_zero]

theorem hxv : Polynomial.eval₂ (algebraMap (ZMod 7) S) xv f7 = 0 := by
  simp only [f7, eval₂_sub, eval₂_pow, eval₂_X, eval₂_ofNat]
  ext <;> simp [xv, mul_pow, hα] <;> first | linear_combination (2:A) * h7 | linear_combination (18:A) * h7

def ι2 : A →ₐ[ZMod 7] S := AdjoinRoot.liftAlgHom f7 (Algebra.ofId (ZMod 7) S) xv hxv

def Φ : TensorProduct (ZMod 7) A A →ₐ[ZMod 7] S := Algebra.TensorProduct.lift D ι2 (fun _ _ => Commute.all _ _)

theorem Φ_tmul (a b : A) : Φ (a ⊗ₜ b) = D a * ι2 b := by
  simp [Φ, Algebra.TensorProduct.lift_tmul]

theorem hι : ι2 α = xv := by
  unfold α ι2
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

theorem hΦα : Φ (α ⊗ₜ 1) = D α := by
  rw [Φ_tmul, map_one, mul_one]

theorem hΦ1 : Φ (1 ⊗ₜ α) = xv := by
  rw [Φ_tmul, map_one, one_mul, hι]

def E1 : TensorProduct (ZMod 7) A A := 6 * (α ⊗ₜ 1) * ((1 ⊗ₜ α) - 2 * (α ⊗ₜ 1)) * ((1 ⊗ₜ α) - 4 * (α ⊗ₜ 1))
def E2 : TensorProduct (ZMod 7) A A := 5 * α ⊗ₜ 1 * ((1 ⊗ₜ α) - (α ⊗ₜ 1)) * ((1 ⊗ₜ α) - 4 * (α ⊗ₜ 1))
def E3 : TensorProduct (ZMod 7) A A := 3 * α ⊗ₜ 1 * ((1 ⊗ₜ α) - (α ⊗ₜ 1)) * ((1 ⊗ₜ α) - 2 * (α ⊗ₜ 1))

theorem hE1 : Φ E1 = (1, (0, 0)) := by
  simp only [E1, map_mul, map_sub, map_ofNat, hΦα, hΦ1]
  ext <;> simp [D, xv]
  all_goals first | linear_combination 18*hα + 5*h7 | linear_combination (-10)*hα - 3*h7

theorem hE2 : Φ E2 = (0, (1, 0)) := by
  simp only [E2, map_mul, map_sub, map_ofNat, hΦα, hΦ1]
  ext <;> simp [D, xv]
  all_goals first | linear_combination 18*hα + 5*h7 | linear_combination (-10)*hα - 3*h7

theorem hE3 : Φ E3 = (0, (0, 1)) := by
  simp only [E3, map_mul, map_sub, map_ofNat, hΦα, hΦ1]
  ext <;> simp [D, xv]
  all_goals first | linear_combination 18*hα + 5*h7 | linear_combination (-10)*hα - 3*h7

theorem hΦu (u : A) : Φ (u ⊗ₜ 1) = D u := by
  rw [Φ_tmul, map_one, mul_one]

theorem surjΦ : Function.Surjective Φ := by
  intro t
  refine ⟨(t.1 ⊗ₜ 1) * E1 + (t.2.1 ⊗ₜ 1) * E2 + (t.2.2 ⊗ₜ 1) * E3, ?_⟩
  simp only [map_add, map_mul, hΦu, hE1, hE2, hE3]
  ext <;> simp [D]

abbrev f1 : S := (0, (1, 1))
abbrev f2 : S := (1, (0, 1))
abbrev f3 : S := (1, (1, 0))
abbrev e1 : S := (1, (0, 0))
abbrev e2 : S := (0, (1, 0))
abbrev e3 : S := (0, (0, 1))

theorem gen (q : Ideal S) [q.IsPrime] (g e : S) (hg : g ∈ q) (hge : g + e = 1)
    (hinv : ∀ x : S, x * e ≠ 0 → ∃ y : S, y * (x * e) = e) : q = Ideal.span {g} := by
  apply le_antisymm
  · intro x hx
    by_cases h : x * e = 0
    · rw [Ideal.mem_span_singleton]
      exact ⟨x, by linear_combination h - x * hge⟩
    · exfalso
      obtain ⟨y, hy⟩ := hinv x h
      have hxe : x * e ∈ q := Ideal.mul_mem_right _ _ hx
      have he : e ∈ q := by
        rw [← hy]; exact Ideal.mul_mem_left _ _ hxe
      have h1 : (1 : S) ∈ q := by
        rw [← hge]; exact add_mem hg he
      exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one q).mpr h1)
  · exact Ideal.span_le.mpr (by simpa using hg)

theorem inv1 : ∀ x : S, x * e1 ≠ 0 → ∃ y : S, y * (x * e1) = e1 := by
  intro x h
  have hx1 : x.1 ≠ 0 := by
    intro h1; apply h; ext <;> simp [e1, h1]
  exact ⟨(x.1⁻¹, (0, 0)), by ext <;> simp [e1, hx1]⟩

theorem inv2 : ∀ x : S, x * e2 ≠ 0 → ∃ y : S, y * (x * e2) = e2 := by
  intro x h
  have hx1 : x.2.1 ≠ 0 := by
    intro h1; apply h; ext <;> simp [e2, h1]
  exact ⟨(0, (x.2.1⁻¹, 0)), by ext <;> simp [e2, hx1]⟩

theorem inv3 : ∀ x : S, x * e3 ≠ 0 → ∃ y : S, y * (x * e3) = e3 := by
  intro x h
  have hx1 : x.2.2 ≠ 0 := by
    intro h1; apply h; ext <;> simp [e3, h1]
  exact ⟨(0, (0, x.2.2⁻¹)), by ext <;> simp [e3, hx1]⟩

theorem principal_S (q : Ideal S) [q.IsPrime] : q.IsPrincipal := by
  have hprod : f1 * f2 * f3 = 0 := by ext <;> simp
  have h0 : f1 * f2 * f3 ∈ q := by rw [hprod]; exact q.zero_mem
  rcases (inferInstance : q.IsPrime).mem_or_mem h0 with h | h
  · rcases (inferInstance : q.IsPrime).mem_or_mem h with h' | h'
    · exact ⟨⟨f1, gen q f1 e1 h' (by ext <;> simp [f1, e1]) inv1⟩⟩
    · exact ⟨⟨f2, gen q f2 e2 h' (by ext <;> simp [f2, e2]) inv2⟩⟩
  · exact ⟨⟨f3, gen q f3 e3 h (by ext <;> simp [f3, e3]) inv3⟩⟩

theorem surj_bij : Function.Bijective (Φ : TensorProduct (ZMod 7) A A →ₐ[ZMod 7] S).toRingHom := by
  have hinj : Function.Injective (Φ.toLinearMap) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finT.trans finS.symm)).mpr surjΦ
  exact ⟨hinj, surjΦ⟩

theorem final_thm (p : Ideal (TensorProduct (ZMod 7) A A)) [p.IsPrime] : p.IsPrincipal := by
  let e : TensorProduct (ZMod 7) A A ≃+* S := RingEquiv.ofBijective _ surj_bij
  have hq : (Ideal.map (e : TensorProduct (ZMod 7) A A →+* S) p).IsPrime := Ideal.map_isPrime_of_equiv e
  have := hq
  have := principal_S (Ideal.map (e : TensorProduct (ZMod 7) A A →+* S) p)
  obtain ⟨g, hg⟩ := (inferInstance : (Ideal.map (e : TensorProduct (ZMod 7) A A →+* S) p).IsPrincipal).principal
  have key : ∀ x, x ∈ p ↔ e x ∈ Ideal.map (e : TensorProduct (ZMod 7) A A →+* S) p := by
    intro x
    have h2 := Ideal.comap_map_of_bijective (e : TensorProduct (ZMod 7) A A →+* S) e.bijective (I := p)
    constructor
    · exact fun hx => Ideal.mem_map_of_mem _ hx
    · intro hx
      have h3 : x ∈ Ideal.comap (e : TensorProduct (ZMod 7) A A →+* S) (Ideal.map (e : TensorProduct (ZMod 7) A A →+* S) p) := hx
      rw [h2] at h3
      exact h3
  refine ⟨⟨e.symm g, ?_⟩⟩
  ext x
  rw [key, hg, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨e.symm c, by apply e.injective; simp [hc]⟩
  · rintro ⟨c, hc⟩
    exact ⟨e c, by rw [hc]; simp⟩

end Fate67

end

/--
Prove that the prime ideals of $\mathbb{F}_7[\alpha] \otimes_{\mathbb{F}_7} \mathbb{F}_7[\alpha]$ are principal, where $\alpha^3 = 2$.
-/
theorem isPrincipal_of_ideal_tensor_zMod_seven
    (p : Ideal (TensorProduct (ZMod 7) (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7)))
    (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))))) [p.IsPrime] : p.IsPrincipal := 
  Fate67.final_thm p
