import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-758»

open scoped RealInnerProductSpace

def IsDescentDirection {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) : Prop :=
  ⟪gradient f x, p⟫ < 0

def SatisfiesWolfeConditions {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ c₂ α : ℝ) : Prop :=
  0 < α ∧
    0 < c₁ ∧
    c₁ < c₂ ∧
    c₂ < 1 ∧
    f (x + α • p) ≤ f x + c₁ * α * ⟪gradient f x, p⟫ ∧
    c₂ * ⟪gradient f x, p⟫ ≤ ⟪gradient f (x + α • p), p⟫

def SatisfiesArmijoCondition {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ α : ℝ) : Prop :=
  0 < α ∧
    0 < c₁ ∧
    c₁ < 1 ∧
    f (x + α • p) ≤ f x + c₁ * α * ⟪gradient f x, p⟫

def SatisfiesCurvatureCondition {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₂ α : ℝ) : Prop :=
  0 < α ∧
    0 < c₂ ∧
    c₂ < 1 ∧
    c₂ * ⟪gradient f x, p⟫ ≤ ⟪gradient f (x + α • p), p⟫

theorem exists_stepSize_satisfying_wolfe_conditions
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) (c₁ c₂ : ℝ)
    (hf : Differentiable ℝ f)
    (hdesc : IsDescentDirection f x p)
    (hbounded : BddBelow (Set.range fun α : Set.Ici (0 : ℝ) => f (x + (α : ℝ) • p)))
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) :
    ∃ α : ℝ, SatisfiesWolfeConditions f x p c₁ c₂ α := by
  have hderiv : ∀ α : ℝ, HasDerivAt (fun t : ℝ => f (x + t • p)) ⟪gradient f (x + α • p), p⟫ α := by
    intro α
    have h1 : HasFDerivAt f (fderiv ℝ f (x + α • p)) (x + α • p) := (hf _).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => x + t • p) p α := by
      simpa using ((hasDerivAt_id α).smul_const p).const_add x
    have hinner : fderiv ℝ f (x + α • p) p = ⟪gradient f (x + α • p), p⟫ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [← hinner]
    exact h1.comp_hasDerivAt α h2
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun t => f (x + t • p) - (f x + c₁ * t * ⟪gradient f x, p⟫) :=
    ⟨_, rfl⟩
  have hgt : ∀ t, g t = f (x + t • p) - (f x + c₁ * t * ⟪gradient f x, p⟫) := by
    intro t; rw [hgdef]
  have hgdiff : ∀ t, HasDerivAt g (⟪gradient f (x + t • p), p⟫ - c₁ * ⟪gradient f x, p⟫) t := by
    intro t
    rw [hgdef]
    exact ((hderiv t).sub ((((hasDerivAt_id t).const_mul c₁).mul_const
      ⟪gradient f x, p⟫).const_add (f x))).congr_deriv (by ring)
  have gcont : Continuous g :=
    continuous_iff_continuousAt.2 fun t => (hgdiff t).continuousAt
  have hg0 : g 0 = 0 := by rw [hgt]; simp
  have hD : ⟪gradient f (x + (0:ℝ) • p), p⟫ - c₁ * ⟪gradient f x, p⟫ < 0 := by
    simp only [zero_smul, add_zero]
    nlinarith [mul_pos hc₁ (neg_pos.2 hdesc)]
  have hg0d := hgdiff 0
  have hT := hasDerivAt_iff_tendsto_slope.mp hg0d
  have hev : ∀ᶠ t in 𝓝[≠] (0:ℝ), slope g 0 t < 0 :=
    hT.eventually_lt_const hD
  have hev2 : ∀ᶠ t in 𝓝 (0:ℝ), t ≠ 0 → slope g 0 t < 0 := by
    rw [eventually_nhdsWithin_iff] at hev; exact hev
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev2
  have hneg : ∀ t, 0 < t → t < ε → g t < 0 := by
    intro t ht htε
    have h := hball (y := t) (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htε) (ne_of_gt ht)
    rw [slope_def_field, hg0] at h
    rcases div_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  obtain ⟨m, hm⟩ := hbounded
  have hm' : ∀ t : ℝ, 0 ≤ t → m ≤ f (x + t • p) := fun t ht => hm ⟨⟨t, Set.mem_Ici.2 ht⟩, rfl⟩
  have hk : 0 < c₁ * (-⟪gradient f x, p⟫) := mul_pos hc₁ (neg_pos.2 hdesc)
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (|f x - m| + 1) / (c₁ * (-⟪gradient f x, p⟫)) := ⟨_, rfl⟩
  have hβpos : 0 < β := by rw [hβdef]; exact div_pos (by positivity) hk
  have hβk : β * (c₁ * (-⟪gradient f x, p⟫)) = |f x - m| + 1 := by
    rw [hβdef]; exact div_mul_cancel₀ _ hk.ne'
  have hgβ : 0 ≤ g β := by
    rw [hgt]
    have e : c₁ * β * ⟪gradient f x, p⟫ = -(β * (c₁ * (-⟪gradient f x, p⟫))) := by ring
    have := hm' β hβpos.le
    have := le_abs_self (f x - m)
    have := abs_nonneg (f x - m)
    rw [e, hβk]; linarith
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = min (ε / 2) β := ⟨_, rfl⟩
  have hδ'pos : 0 < δ' := by rw [hδ']; exact lt_min (by linarith) hβpos
  have hδ'le : δ' ≤ β := by rw [hδ']; exact min_le_right _ _
  have hδ'ε : δ' < ε := by rw [hδ']; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hK : IsCompact (Set.Icc δ' β ∩ {t | 0 ≤ g t}) :=
    isCompact_Icc.inter_right (isClosed_le continuous_const gcont)
  have hβK : β ∈ Set.Icc δ' β ∩ {t | 0 ≤ g t} := ⟨⟨hδ'le, le_refl _⟩, hgβ⟩
  obtain ⟨α₀, hα₀K, hmin⟩ := hK.exists_isMinOn ⟨β, hβK⟩ continuousOn_id
  have hmin' : ∀ t ∈ Set.Icc δ' β ∩ {t | 0 ≤ g t}, α₀ ≤ t := fun t ht => isMinOn_iff.mp hmin t ht
  have hα₀I : δ' ≤ α₀ := hα₀K.1.1
  have hα₀pos : 0 < α₀ := lt_of_lt_of_le hδ'pos hα₀I
  have hgneg : ∀ t, 0 < t → t < α₀ → g t < 0 := by
    intro t ht htα
    by_cases htd : t < δ'
    · exact hneg t ht (lt_trans htd hδ'ε)
    · by_contra hcon
      push_neg at hcon
      have := hmin' t ⟨⟨by linarith [not_lt.1 htd], by linarith [hα₀K.1.2]⟩, hcon⟩
      linarith
  have hg_α₀ : g α₀ = 0 := by
    have hle : g α₀ ≤ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨ρ, hρ, hball2⟩ := Metric.eventually_nhds_iff.mp ((gcont.tendsto α₀).eventually (lt_mem_nhds h))
      have hm1 : 0 < min ρ α₀ := lt_min hρ hα₀pos
      have hm2 : min ρ α₀ ≤ ρ := min_le_left _ _
      have hm3 : min ρ α₀ ≤ α₀ := min_le_right _ _
      have hy := hball2 (y := α₀ - min ρ α₀ / 2) (by
        rw [Real.dist_eq, show α₀ - min ρ α₀ / 2 - α₀ = -(min ρ α₀ / 2) by ring, abs_neg,
          abs_of_pos (by linarith)]
        linarith)
      have := hgneg (α₀ - min ρ α₀ / 2) (by linarith) (by linarith)
      linarith
    have hge : 0 ≤ g α₀ := hα₀K.2
    linarith
  have e1 : f (x + α₀ • p) = f x + c₁ * α₀ * ⟪gradient f x, p⟫ := by
    have := hg_α₀; rw [hgt] at this; linarith
  obtain ⟨α₁, hα₁, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun t : ℝ => f (x + t • p)) (fun t : ℝ => ⟪gradient f (x + t • p), p⟫) hα₀pos
    (fun t _ => ((hderiv t).continuousAt).continuousWithinAt)
    (fun t _ => hderiv t)
  simp only [zero_smul, add_zero] at hslope
  rw [e1, sub_zero, show f x + c₁ * α₀ * ⟪gradient f x, p⟫ - f x = c₁ * ⟪gradient f x, p⟫ * α₀ by ring,
    mul_div_assoc, div_self hα₀pos.ne', mul_one] at hslope
  have hα₁g := hgneg α₁ hα₁.1 hα₁.2
  rw [hgt] at hα₁g
  refine ⟨α₁, hα₁.1, hc₁, hc₁₂, hc₂, ?_, ?_⟩
  · linarith
  · rw [hslope]
    nlinarith [mul_pos (sub_pos.2 hc₁₂) (neg_pos.2 hdesc)]

end «CAM-Bench-758»
