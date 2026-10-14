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
  obtain ⟨B1, B2, hB⟩ := hgbd
  have hpos1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hpos2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have hE : ∀ s x, g1 s ^ x * g2 s = Real.exp (Real.log (g1 s) * x + Real.log (g2 s)) := by
    intro s x
    rw [Real.rpow_def_of_pos (hpos1 s), Real.exp_add, Real.exp_log (hpos2 s)]
  have hB1 : 1 ≤ B1 := le_trans (hgim 0).1 (hB 0).1
  have hB2 : 1 ≤ B2 := le_trans (hgim 0).2 (hB 0).2
  have hL1 : 0 ≤ Real.log B1 := Real.log_nonneg hB1
  have hL2 : 0 ≤ Real.log B2 := Real.log_nonneg hB2
  have hloga : ∀ s, 0 ≤ Real.log (g1 s) := fun s => Real.log_nonneg (hgim s).1
  have hlogaB : ∀ s, Real.log (g1 s) ≤ Real.log B1 := fun s =>
    Real.log_le_log (hpos1 s) (hB s).1
  have hbound : ∀ s x, g1 s ^ x * g2 s ≤ Real.exp (Real.log B1 * |x| + Real.log B2) := by
    intro s x
    rw [hE]
    apply Real.exp_le_exp.mpr
    have h1 := hloga s
    have h2 := hlogaB s
    have h3 : Real.log (g2 s) ≤ Real.log B2 := Real.log_le_log (hpos2 s) (hB s).2
    have h4 : Real.log (g1 s) * x ≤ Real.log (g1 s) * |x| :=
      mul_le_mul_of_nonneg_left (le_abs_self x) h1
    have h5 : Real.log (g1 s) * |x| ≤ Real.log B1 * |x| :=
      mul_le_mul_of_nonneg_right h2 (abs_nonneg x)
    linarith
  have hbddL : ∀ x : ℝ, BddAbove {y | ∃ s : ℝ, g1 s ^ x * g2 s = y} := by
    intro x
    exact ⟨_, by rintro y ⟨s, rfl⟩; exact hbound s x⟩
  obtain ⟨e⟩ : Nonempty (ℝ ≃ ℝ × ℝ) := by
    apply Cardinal.eq.1
    simp [Cardinal.mk_real, Cardinal.continuum_mul_self]
  let p : ℝ → ℝ × ℝ := fun t => e t
  have hp : ∀ q : ℝ × ℝ, ∃ t, p t = q := fun q => ⟨e.symm q, by simp [p]⟩
  let T : ℝ × ℝ → ℝ := fun q => Real.exp (Real.log (g1 q.1) * q.2 + Real.log (g2 q.1))
  have hTpos : ∀ q, 0 < T q := fun q => Real.exp_pos _
  refine ⟨fun t => Real.log (g1 (p t).1) * T (p t),
    fun t => T (p t) - (p t).2 * (Real.log (g1 (p t).1) * T (p t)), ?_⟩
  intro x
  beta_reduce
  have htan : ∀ s x0 x : ℝ, T (s, x0) + (x - x0) * (Real.log (g1 s) * T (s, x0))
      ≤ g1 s ^ x * g2 s := by
    intro s x0 x
    rw [hE]
    have hsplit : Real.log (g1 s) * x + Real.log (g2 s)
        = (Real.log (g1 s) * x0 + Real.log (g2 s)) + Real.log (g1 s) * (x - x0) := by ring
    have hT : T (s, x0) = Real.exp (Real.log (g1 s) * x0 + Real.log (g2 s)) := rfl
    rw [hsplit, Real.exp_add]
    have hk := mul_le_mul_of_nonneg_left
      (Real.add_one_le_exp (Real.log (g1 s) * (x - x0))) (hTpos (s, x0)).le
    rw [hT]
    rw [hT] at hk
    nlinarith [hk]
  have hval0 : ∀ t : ℝ, x * (Real.log (g1 (p t).1) * T (p t))
      + (T (p t) - (p t).2 * (Real.log (g1 (p t).1) * T (p t)))
      = T (p t) + (x - (p t).2) * (Real.log (g1 (p t).1) * T (p t)) := fun t => by ring
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨0, rfl⟩⟩
    · rintro y ⟨s, rfl⟩
      obtain ⟨t, ht⟩ := hp (s, x)
      have hval : x * (Real.log (g1 (p t).1) * T (p t))
          + (T (p t) - (p t).2 * (Real.log (g1 (p t).1) * T (p t)))
          = g1 s ^ x * g2 s := by
        rw [ht, hE]
        have hTx : T (s, x) = Real.exp (Real.log (g1 s) * x + Real.log (g2 s)) := rfl
        simp only []
        rw [hTx]
        ring
      rw [← hval]
      have hbR : BddAbove {y | ∃ t : ℝ, x * (Real.log (g1 (p t).1) * T (p t))
          + (T (p t) - (p t).2 * (Real.log (g1 (p t).1) * T (p t))) = y} := by
        refine ⟨sSup {y | ∃ s : ℝ, g1 s ^ x * g2 s = y}, ?_⟩
        rintro y ⟨t, rfl⟩
        rw [hval0 t]
        exact le_trans (htan (p t).1 (p t).2 x) (le_csSup (hbddL x) ⟨(p t).1, rfl⟩)
      exact le_csSup hbR ⟨t, rfl⟩
  · apply csSup_le
    · exact ⟨_, ⟨0, rfl⟩⟩
    · rintro y ⟨t, rfl⟩
      rw [hval0 t]
      exact le_trans (htan (p t).1 (p t).2 x) (le_csSup (hbddL x) ⟨(p t).1, rfl⟩)
