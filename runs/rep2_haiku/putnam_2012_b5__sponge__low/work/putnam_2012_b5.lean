import Mathlib

open Matrix Function Real Topology Filter

/--
Prove that, for any two bounded functions $g_1, g_2: \RR \to [1, \infty)$, there exist functions $h_1, h_2: \RR \to \RR$ such that, for every $x \in \RR$, \[ \sup_{s \in \RR} (g_1(s)^x g_2(s))  = \max_{t \in \RR} (x h_1(t) + h_2(t)).\]
-/
theorem putnam_2012_b5
(g1 g2 : ℝ → ℝ)
(hgim : ∀ x : ℝ, g1 x ≥ 1 ∧ g2 x ≥ 1)
(hgbd : ∃ B1 B2 : ℝ, ∀ x : ℝ, g1 x ≤ B1 ∧ g2 x ≤ B2)
: ∃ h1 h2 : ℝ → ℝ, ∀ x : ℝ, sSup {((g1 s)^x * (g2 s)) | s : ℝ} = sSup {(x * (h1 t) + h2 t) | t : ℝ} :=
by
  classical
  obtain ⟨B1, B2, hB⟩ := hgbd
  obtain ⟨e⟩ : Nonempty (ℝ ≃ ℝ × ℝ) := by
    apply Cardinal.eq.1
    simp [Cardinal.mk_prod]
  have hpos1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hpos2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have ha0 : ∀ s, 0 ≤ Real.log (g1 s) := fun s => Real.log_nonneg (hgim s).1
  have hb0 : ∀ s, 0 ≤ Real.log (g2 s) := fun s => Real.log_nonneg (hgim s).2
  have ha1 : ∀ s, Real.log (g1 s) ≤ Real.log B1 :=
    fun s => Real.log_le_log (hpos1 s) (hB s).1
  have hb1 : ∀ s, Real.log (g2 s) ≤ Real.log B2 :=
    fun s => Real.log_le_log (hpos2 s) (hB s).2
  have hform : ∀ s x, g1 s ^ x * g2 s = Real.exp (Real.log (g1 s) * x + Real.log (g2 s)) := by
    intro s x
    rw [Real.exp_add, Real.rpow_def_of_pos (hpos1 s), Real.exp_log (hpos2 s)]
  have hbdd : ∀ x : ℝ, BddAbove {y | ∃ s, g1 s ^ x * g2 s = y} := by
    intro x
    refine ⟨Real.exp (Real.log B1 * |x| + Real.log B2), ?_⟩
    rintro y ⟨s, rfl⟩
    rw [hform]
    apply Real.exp_le_exp.mpr
    have h1 := ha0 s
    have h2 := ha1 s
    have h3 := hb1 s
    nlinarith [le_abs_self x, abs_nonneg x, mul_le_mul_of_nonneg_right h2 (abs_nonneg x),
      mul_le_mul_of_nonneg_left (le_abs_self x) h1]
  have hminor : ∀ x s u : ℝ, Real.exp (Real.log (g1 s) * u + Real.log (g2 s)) *
      (1 + Real.log (g1 s) * (x - u)) ≤ g1 s ^ x * g2 s := by
    intro x s u
    rw [hform]
    have hsplit : Real.exp (Real.log (g1 s) * x + Real.log (g2 s)) =
        Real.exp (Real.log (g1 s) * u + Real.log (g2 s)) * Real.exp (Real.log (g1 s) * (x - u)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith [Real.add_one_le_exp (Real.log (g1 s) * (x - u))]
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ → ℝ × ℝ, Function.Surjective σ := ⟨e, e.surjective⟩
  let G : ℝ × ℝ → ℝ := fun p => Real.exp (Real.log (g1 p.1) * p.2 + Real.log (g2 p.1))
  let A : ℝ × ℝ → ℝ := fun p => Real.log (g1 p.1) * G p
  have hval : ∀ x : ℝ, ∀ p : ℝ × ℝ, x * A p + (G p - p.2 * A p) =
      G p * (1 + Real.log (g1 p.1) * (x - p.2)) := by
    intro x p
    simp only [A]
    ring
  refine ⟨fun t => A (σ t), fun t => G (σ t) - (σ t).2 * A (σ t), fun x => ?_⟩
  have hup : ∀ t : ℝ, x * A (σ t) + (G (σ t) - (σ t).2 * A (σ t)) ≤
      sSup {y | ∃ s, g1 s ^ x * g2 s = y} := by
    intro t
    rw [hval]
    exact le_trans (hminor x (σ t).1 (σ t).2) (le_csSup (hbdd x) ⟨(σ t).1, rfl⟩)
  have hTbdd : BddAbove {y | ∃ t : ℝ, x * A (σ t) + (G (σ t) - (σ t).2 * A (σ t)) = y} := by
    refine ⟨sSup {y | ∃ s, g1 s ^ x * g2 s = y}, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hup t
  apply le_antisymm
  · apply csSup_le
    · exact ⟨g1 0 ^ x * g2 0, 0, rfl⟩
    rintro y ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := hσ (s, x)
    have hmem : g1 s ^ x * g2 s ∈
        {y | ∃ t : ℝ, x * A (σ t) + (G (σ t) - (σ t).2 * A (σ t)) = y} := by
      refine ⟨t, ?_⟩
      rw [hval, ht]
      simp only [G, sub_self, mul_zero, add_zero, mul_one]
      exact (hform s x).symm
    exact le_csSup hTbdd hmem
  · apply csSup_le
    · exact ⟨x * A (σ 0) + (G (σ 0) - (σ 0).2 * A (σ 0)), 0, rfl⟩
    rintro y ⟨t, rfl⟩
    exact hup t
