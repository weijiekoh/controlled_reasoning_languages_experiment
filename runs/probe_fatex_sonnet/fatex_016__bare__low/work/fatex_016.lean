import Mathlib

namespace Problem16

/--
A Galois extension such that the degree of the extension is a power of a prime \( p \) is
called a p-extension.
-/
class IsPExtension (F E : Type) [Field F] [Field E] [Algebra F E]
    (p : ℕ) : Prop extends IsGalois F E where
    rank_eq_pow : ∃ (n : ℕ), Module.rank F E = p ^ n

/--
Let $p$ be a prime and let $F$ be a field.
Let $K$ be a finite Galois extension of $F$ whose Galois group is a $p$-group (i.e., the degree
$[K : F]$ is a power of $p$). Such an extension is called a \emph{$p$-extension} (note that
$p$-extensions are Galois by definition). Let $L$ be a $p$-extension of $K$. Prove that the
Galois closure of $L$ over $F$ is a $p$-extension of $F$.
-/
theorem normalClosure_isPExtension_of_isPExtension (F E : Type) [Field F] [Field E]
    [Algebra F E] (L : IntermediateField F E) (K : IntermediateField F L) (p : ℕ) (hp : p.Prime)
    [IsPExtension F K p] [IsGalois K L] [IsPExtension K L p]
    (h_normalClosure : IsNormalClosure F L E) : IsPExtension F E p := by
  have hN : Normal F E := h_normalClosure.normal
  have ht : IntermediateField.normalClosure F L E = ⊤ := by
    rw [normalClosure_eq_iSup_adjoin]; exact h_normalClosure.adjoin_rootSet
  have hKfin : FiniteDimensional F K := by
    obtain ⟨n, hn⟩ := (inferInstance : IsPExtension F K p).rank_eq_pow
    apply Module.rank_lt_aleph0_iff.1
    rw [hn]
    have : ((p : Cardinal) ^ n) = ((p ^ n : ℕ) : Cardinal) := by push_cast; rfl
    rw [this]; exact Cardinal.nat_lt_aleph0 _
  have hLfin : FiniteDimensional K L := by
    obtain ⟨n, hn⟩ := (inferInstance : IsPExtension K L p).rank_eq_pow
    apply Module.rank_lt_aleph0_iff.1
    rw [hn]
    have : ((p : Cardinal) ^ n) = ((p ^ n : ℕ) : Cardinal) := by push_cast; rfl
    rw [this]; exact Cardinal.nat_lt_aleph0 _
  have hLfinF : FiniteDimensional F L := FiniteDimensional.trans F K L
  have hLsep : Algebra.IsSeparable F L := Algebra.IsSeparable.trans F K L
  haveI : Fact p.Prime := ⟨hp⟩
  have hKcard : ∃ a, Nat.card (K ≃ₐ[F] K) = p ^ a := by
    obtain ⟨n, hn⟩ := (inferInstance : IsPExtension F K p).rank_eq_pow
    refine ⟨n, ?_⟩
    rw [IsGalois.card_aut_eq_finrank]
    apply Module.finrank_eq_of_rank_eq
    rw [hn]; push_cast; rfl
  have hLcard : ∃ a, Nat.card (L ≃ₐ[K] L) = p ^ a := by
    obtain ⟨n, hn⟩ := (inferInstance : IsPExtension K L p).rank_eq_pow
    refine ⟨n, ?_⟩
    rw [IsGalois.card_aut_eq_finrank]
    apply Module.finrank_eq_of_rank_eq
    rw [hn]; push_cast; rfl
  have hFE : FiniteDimensional F E := by
    have e : (⊤ : IntermediateField F E) ≃ₐ[F] E := IntermediateField.topEquiv
    have : FiniteDimensional F (IntermediateField.normalClosure F L E) := inferInstance
    have e2 : (IntermediateField.normalClosure F L E) ≃ₐ[F] E :=
      (IntermediateField.equivOfEq ht).trans e
    exact LinearEquiv.finiteDimensional e2.toLinearEquiv
  have hSep : Algebra.IsSeparable F E := by
    have h1 : Algebra.IsSeparable F (⊤ : IntermediateField F E) := by
      rw [← h_normalClosure.adjoin_rootSet]
      have hi : ∀ x : L, Algebra.IsSeparable F (IntermediateField.adjoin F ((minpoly F x).rootSet E)) := by
       intro x
       rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
       intro r hr
       have hr' : (Polynomial.aeval r) (minpoly F x) = 0 := by
         rw [Polynomial.mem_rootSet] at hr; exact hr.2
       have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
       have hmin : minpoly F x = minpoly F r :=
         minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr' (minpoly.monic hint)
       have hs : (minpoly F x).Separable := Algebra.IsSeparable.isSeparable F x
       show (minpoly F r).Separable
       rw [← hmin]; exact hs
      exact IntermediateField.isSeparable_iSup F E
    exact Algebra.IsSeparable.of_algHom F _ (IntermediateField.topEquiv (F := F) (E := E)).symm.toAlgHom
  have hG : IsGalois F E := {}
  -- key
  have key : ∀ q : ℕ, q.Prime → q ≠ p → ∀ g : E ≃ₐ[F] E, g ^ q = 1 → g = 1 := by
    intro q hq hqp
    have hcop : ∀ a : ℕ, Nat.Coprime q (p ^ a) := fun a =>
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hq hp).2 hqp)
    have keyL : ∀ g : E ≃ₐ[F] E, g ^ q = 1 → ∀ x : L, g (x : E) = x := by
      intro g hg
      -- fixes K
      have hK : ∀ k : K, g ((k : L) : E) = ((k : L) : E) := by
        obtain ⟨a, ha⟩ := hKcard
        let φ : (E ≃ₐ[F] E) →* (K ≃ₐ[F] K) := AlgEquiv.restrictNormalHom K
        have h1 : orderOf (φ g) ∣ q := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg, map_one])
        have h2 : orderOf (φ g) ∣ p ^ a := ha ▸ orderOf_dvd_natCard _
        have h3 : orderOf (φ g) = 1 := Nat.eq_one_of_dvd_coprimes (hcop a) h1 h2 |> fun h => by simpa using h
        have h4 : φ g = 1 := orderOf_eq_one_iff.1 h3
        intro k
        have := AlgEquiv.restrictNormal_commutes g K k
        have h5 : g.restrictNormal K = 1 := h4
        rw [h5] at this
        simp only [AlgEquiv.one_apply] at this
        exact this.symm
      let g' : E ≃ₐ[K] E :=
        { g with commutes' := fun k => hK k }
      obtain ⟨a, ha⟩ := hLcard
      let ψ : (E ≃ₐ[K] E) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
      have hg' : g' ^ q = 1 := by
        ext x
        have : (g ^ q) x = x := by rw [hg]; rfl
        simpa [g'] using this
      have h1 : orderOf (ψ g') ∣ q := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hg', map_one])
      have h2 : orderOf (ψ g') ∣ p ^ a := ha ▸ orderOf_dvd_natCard _
      have h3 : orderOf (ψ g') = 1 := Nat.eq_one_of_dvd_coprimes (hcop a) h1 h2 |> fun h => by simpa using h
      have h4 : ψ g' = 1 := orderOf_eq_one_iff.1 h3
      intro x
      have := AlgEquiv.restrictNormal_commutes g' L x
      have h5 : g'.restrictNormal L = 1 := h4
      rw [h5] at this
      simp only [AlgEquiv.one_apply] at this
      exact this.symm
    intro g hg
    have hall : ∀ σ : E ≃ₐ[F] E, ∀ x : L, g (σ (x : E)) = σ (x : E) := by
      intro σ x
      have h1 : (σ⁻¹ * g * σ) ^ q = 1 := by
        have : (σ⁻¹ * g * σ⁻¹⁻¹) ^ q = σ⁻¹ * g ^ q * σ⁻¹⁻¹ := conj_pow
        simp only [inv_inv] at this
        rw [this, hg]; simp
      have := keyL _ h1 x
      have h2 : σ⁻¹ (g (σ (x:E))) = x := this
      have h3 := congrArg σ h2
      simpa using h3
    have hle : (⨆ x : L, IntermediateField.adjoin F ((minpoly F x).rootSet E))
        ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
      apply iSup_le
      intro x
      rw [IntermediateField.adjoin_le_iff]
      intro r hr
      have hr' : (Polynomial.aeval r) (minpoly F x) = 0 := by
        rw [Polynomial.mem_rootSet] at hr; exact hr.2
      have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
      have hmin : minpoly F x = minpoly F r :=
        minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr' (minpoly.monic hint)
      have hmin2 : minpoly F r = minpoly F (x : E) := by
        rw [← hmin]; exact (IntermediateField.minpoly_eq x)
      obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit E).1 hmin2
      have hσ' : σ (x : E) = r := hσ
      have hfix : g • r = r := by
        rw [← hσ']; exact hall σ x
      show r ∈ IntermediateField.fixedField (Subgroup.zpowers g)
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      have : Subgroup.zpowers g ≤ MulAction.stabilizer (E ≃ₐ[F] E) r :=
        (Subgroup.zpowers_le).2 (MulAction.mem_stabilizer_iff.2 hfix)
      exact this hf
    rw [h_normalClosure.adjoin_rootSet] at hle
    ext x
    have : x ∈ IntermediateField.fixedField (Subgroup.zpowers g) := hle trivial
    rw [IntermediateField.mem_fixedField_iff] at this
    simpa using this g (Subgroup.mem_zpowers g)
  have hP : IsPGroup p (E ≃ₐ[F] E) := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := p) (fun {q} hq hd => by
      by_contra hqp
      have hqpos := hq.pos
      have hh : (g ^ (orderOf g / q)) ^ q = 1 := by
        rw [← pow_mul, Nat.div_mul_cancel hd]; exact pow_orderOf_eq_one g
      have := key q hq hqp _ hh
      have h2 := orderOf_dvd_of_pow_eq_one this
      have h3 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hd) hqpos) h2
      have : orderOf g / q < orderOf g := Nat.div_lt_self (Nat.pos_of_ne_zero hpos) hq.one_lt
      omega)
    exact ⟨_, this⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  refine { hG with rank_eq_pow := ⟨n, ?_⟩ }
  rw [← Module.finrank_eq_rank, ← IsGalois.card_aut_eq_finrank, hn]
  push_cast; rfl

end Problem16
