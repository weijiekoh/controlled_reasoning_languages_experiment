import Mathlib
open Polynomial IntermediateField

theorem twogen (K L : Type) [Field K] [Field L] [Algebra K L] [Infinite K]
    (α β : L) (hα : IsIntegral K α) (hβ : IsSeparable K β) :
    ∃ γ : L, K⟮α, β⟯ = K⟮γ⟯ := by
  have hβi : IsIntegral K β := hβ.isIntegral
  set f := minpoly K α with hf
  set g := minpoly K β with hg
  have hf0 : f ≠ 0 := minpoly.ne_zero hα
  have hg0 : g ≠ 0 := minpoly.ne_zero hβi
  let Ω := SplittingField ((f * g).map (algebraMap K L))
  let ϕ : K →+* Ω := (algebraMap L Ω).comp (algebraMap K L)
  let α' : Ω := algebraMap L Ω α
  let β' : Ω := algebraMap L Ω β
  obtain ⟨c, hc⟩ := Field.primitive_element_inf_aux_exists_c ϕ α' β' f g
  have hsplit : ((f * g).map ϕ).Splits := by
    have := IsSplittingField.splits Ω ((f * g).map (algebraMap K L))
    rwa [Polynomial.map_map] at this
  have hfg0 : (f * g).map ϕ ≠ 0 := by
    simpa using mul_ne_zero hf0 hg0
  have hgs : (g.map ϕ).Splits :=
    Splits.of_dvd hsplit hfg0 (by simpa using Polynomial.map_dvd ϕ (dvd_mul_left g f))
  set γ : L := α + algebraMap K L c * β with hγ
  have key : β ∈ K⟮γ⟯ := by
    set E := K⟮γ⟯ with hE
    let γE : E := ⟨γ, mem_adjoin_simple_self K γ⟩
    let m := minpoly E β
    let ψ : E →+* Ω := (algebraMap L Ω).comp (E.val : E →+* L)
    have hψ : ψ.comp (algebraMap K E) = ϕ := by ext x; rfl
    have hmg : m ∣ g.map (algebraMap K E) := minpoly.dvd_map_of_isScalarTower K E β
    let h : E[X] := (f.map (algebraMap K E)).comp (C γE - C (algebraMap K E c) * X)
    have hmh : m ∣ h := by
      apply minpoly.dvd
      have : aeval β (C γE - C (algebraMap K E c) * X) = α := by
        simp [γE, hγ]
      simp only [h, aeval_comp, this]
      rw [aeval_map_algebraMap]
      exact minpoly.aeval K α
    have hmi : IsIntegral E β := hβi.tower_top
    have hm0 : m.map ψ ≠ 0 := by
      have := minpoly.ne_zero hmi
      simpa using this
    have h1 : m.map ψ ∣ g.map ϕ := by
      rw [← hψ, ← Polynomial.map_map]; exact Polynomial.map_dvd ψ hmg
    have h2 : m.map ψ ∣ h.map ψ := Polynomial.map_dvd ψ hmh
    have hsp : (m.map ψ).Splits := Splits.of_dvd hgs (by simpa using hg0) h1
    have hsep : (m.map ψ).Separable := by
      have : (g.map ϕ).Separable := hβ.map
      exact this.of_dvd h1
    have hall : ∀ r ∈ (m.map ψ).roots, r = β' := by
      intro r hr
      have hr' : (m.map ψ).IsRoot r := (mem_roots hm0).1 hr
      have hrg : (g.map ϕ).IsRoot r := by
        obtain ⟨q, hq⟩ := h1
        simp [hq, hr'.eq_zero]
      have hrh : (h.map ψ).IsRoot r := by
        obtain ⟨q, hq⟩ := h2
        simp [hq, hr'.eq_zero]
      by_contra hne
      have hf0' : f.map ϕ ≠ 0 := by simpa using hf0
      have hroot : (γ' : Ω) ∈ (0 : Ω) := sorry
      sorry
    sorry
  sorry
