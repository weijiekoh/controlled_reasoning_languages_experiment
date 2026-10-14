import Mathlib

open Polynomial

/--
Let $K$ be the splitting field of a irreducible quintic polynomial $f(x) \in \mathbb{Q} [x]$
and let $\{\alpha_1, \dots, \alpha_5\}$ be zeros of $f(x)$ in $K$. Show that if $\mathbb{Q}
(\alpha_1, \alpha_2, \alpha_3) \neq K$, then $\\mathrm{Gal}(K/\mathbb{Q}) \cong S_5$.
-/
theorem nonempty_gal_mulEquiv_perm_fin_five {f : ℚ[X]} {K : Type} [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K f] (hf1 : Irreducible f) (hf2 : f.natDegree = 5) (a₁ a₂ a₃ : K)
    (ha1 : a₁ ∈ rootSet f K ∧ a₂ ∈ rootSet f K ∧ a₃ ∈ rootSet f K)
    (ha2 : a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₃ ≠ a₁)
    (h : IntermediateField.adjoin ℚ {a₁, a₂, a₃} ≠ ⊤) :
    Nonempty (f.Gal ≃* (Equiv.Perm <| Fin 5)) := by
  classical
  obtain ⟨h1', h2', h3'⟩ := ha1
  obtain ⟨n12', n23', n31'⟩ := ha2
  have key5 : ∀ p : Equiv.Perm (Fin 5), ∀ x y z : Fin 5, x ≠ y → y ≠ z → x ≠ z → p x = x →
      p y = y → p z = z → p ≠ 1 → ∃ u v : Fin 5, u ≠ v ∧ p = Equiv.swap u v := by
    set_option maxRecDepth 100000 in decide
  -- transfer everything to the splitting field `L` of `f` used by `f.Gal`
  let φ : K ≃ₐ[ℚ] f.SplittingField := IsSplittingField.algEquiv K f
  have hmem : ∀ a : K, a ∈ rootSet f K → φ a ∈ rootSet f f.SplittingField := by
    intro a ha
    rw [Polynomial.mem_rootSet] at ha ⊢
    refine ⟨ha.1, ?_⟩
    rw [show φ a = φ.toAlgHom a from rfl, Polynomial.aeval_algHom_apply, ha.2, map_zero]
  have hφinj : Function.Injective φ := φ.injective
  have h1 := hmem a₁ h1'
  have h2 := hmem a₂ h2'
  have h3 := hmem a₃ h3'
  have n12 : φ a₁ ≠ φ a₂ := fun e => n12' (hφinj e)
  have n23 : φ a₂ ≠ φ a₃ := fun e => n23' (hφinj e)
  have n31 : φ a₃ ≠ φ a₁ := fun e => n31' (hφinj e)
  have h' : IntermediateField.adjoin ℚ {φ a₁, φ a₂, φ a₃} ≠ ⊤ := by
    intro heq
    apply h
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ IntermediateField.adjoin ℚ {φ a₁, φ a₂, φ a₃} := by rw [heq]; trivial
    have hmap : IntermediateField.map φ.toAlgHom (IntermediateField.adjoin ℚ {a₁, a₂, a₃})
        = IntermediateField.adjoin ℚ {φ a₁, φ a₂, φ a₃} := by
      rw [IntermediateField.adjoin_map]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with rfl | rfl | rfl <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨a₁, by simp, rfl⟩
        · exact ⟨a₂, by simp, rfl⟩
        · exact ⟨a₃, by simp, rfl⟩
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := (IntermediateField.mem_map _).1 hx
    have : y = x := hφinj hyx
    rw [← this]; exact hy
  have main : ∀ b1 b2 b3 : f.SplittingField, b1 ∈ rootSet f f.SplittingField →
      b2 ∈ rootSet f f.SplittingField → b3 ∈ rootSet f f.SplittingField →
      b1 ≠ b2 → b2 ≠ b3 → b3 ≠ b1 →
      IntermediateField.adjoin ℚ {b1, b2, b3} ≠ ⊤ →
      Nonempty (f.Gal ≃* (Equiv.Perm <| Fin 5)) := by
    intro a₁ a₂ a₃ h1 h2 h3 n12 n23 n31 h
    have hsep : f.Separable := hf1.separable
    haveI hF : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits :=
      Fact.mk (SplittingField.splits f)
    have hsplf : IsSplittingField ℚ f.SplittingField f :=
      ⟨SplittingField.splits f, SplittingField.adjoin_rootSet f⟩
    have : IsGalois ℚ f.SplittingField := IsGalois.of_separable_splitting_field hsep
    have hcard : Fintype.card (f.rootSet f.SplittingField) = 5 := by
      exact (Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits f)).trans hf2
    let e : (f.rootSet f.SplittingField) ≃ Fin 5 := Fintype.equivFinOfCardEq hcard
    let c : Equiv.Perm (f.rootSet f.SplittingField) →* Equiv.Perm (Fin 5) :=
      { toFun := fun p => e.permCongr p
        map_one' := by ext x; simp [Equiv.permCongr_apply]
        map_mul' := by intro p q; ext x; simp [Equiv.permCongr_apply] }
    let ψ0 : f.Gal →* Equiv.Perm (f.rootSet f.SplittingField) :=
      (Polynomial.Gal.galActionHom f f.SplittingField).comp
        (Polynomial.Gal.restrict f f.SplittingField)
    let ψ : f.Gal →* Equiv.Perm (Fin 5) := c.comp ψ0
    have hψinj : Function.Injective ψ := by
      have test : Fact (Polynomial.map (algebraMap ℚ f.SplittingField) f).Splits := inferInstance
      have test2 := Polynomial.Gal.galActionHom_restrict f f.SplittingField σ0
      intro σ τ hst
      have h0 : ψ0 σ = ψ0 τ := (Equiv.permCongr e).injective hst
      have hres : Polynomial.Gal.restrict f f.SplittingField σ =
          Polynomial.Gal.restrict f f.SplittingField τ :=
        Polynomial.Gal.galActionHom_injective f f.SplittingField h0
      apply AlgEquiv.ext
      intro y
      have hext := AlgHom.ext_of_adjoin_eq_top (SplittingField.adjoin_rootSet f)
        (φ₁ := σ.toAlgHom) (φ₂ := τ.toAlgHom) (fun x hx => by
          have e1 := Polynomial.Gal.galActionHom_restrict f f.SplittingField σ ⟨x, hx⟩
          have e2 := Polynomial.Gal.galActionHom_restrict f f.SplittingField τ ⟨x, hx⟩
          rw [hres] at e1
          exact e1.symm.trans e2)
      exact DFunLike.congr_fun hext y
    have hfix : ∀ σ : f.Gal, ∀ a (ha : a ∈ f.rootSet f.SplittingField), σ a = a →
        ψ σ (e ⟨a, ha⟩) = e ⟨a, ha⟩ := by
      intro σ a ha hσ
      show e ((Polynomial.Gal.galActionHom f f.SplittingField)
        (Polynomial.Gal.restrict f f.SplittingField σ) (e.symm (e ⟨a, ha⟩))) = e ⟨a, ha⟩
      rw [Equiv.symm_apply_apply]
      congr 1
      apply Subtype.ext
      have e1 := Polynomial.Gal.galActionHom_restrict f f.SplittingField
        (Polynomial.Gal.restrict f f.SplittingField σ) ⟨a, ha⟩
      sorry
    sorry
  exact main _ _ _ h1 h2 h3 n12 n23 n31 h'
