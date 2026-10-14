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
  have pos1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have pos2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  obtain ⟨e⟩ : Nonempty (ℝ ≃ ℝ × ℝ) := by
    rw [← Cardinal.eq]; simp
  refine ⟨fun t => (g1 (e t).1)^(e t).2 * g2 (e t).1 * Real.log (g1 (e t).1),
    fun t => (g1 (e t).1)^(e t).2 * g2 (e t).1 * (1 - (e t).2 * Real.log (g1 (e t).1)), ?_⟩
  intro x
  have bdd : BddAbove {((g1 s)^x * (g2 s)) | s : ℝ} := by
    refine ⟨max 1 (B1^x) * B2, ?_⟩
    rintro _ ⟨s, rfl⟩
    have h1 : (g1 s)^x ≤ max 1 (B1^x) := by
      rcases le_or_gt 0 x with hx | hx
      · exact le_trans (Real.rpow_le_rpow (by linarith [(hgim s).1]) (hB s).1 hx) (le_max_right _ _)
      · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos (hgim s).1 hx.le) (le_max_left _ _)
    have := (hB s).2
    have := (hgim s).2
    have : 0 ≤ (g1 s)^x := (Real.rpow_pos_of_pos (pos1 s) x).le
    exact mul_le_mul h1 (hB s).2 (by linarith [(hgim s).2]) (le_trans this h1)
  have key : ∀ t, x * ((g1 (e t).1)^(e t).2 * g2 (e t).1 * Real.log (g1 (e t).1)) + (g1 (e t).1)^(e t).2 * g2 (e t).1 * (1 - (e t).2 * Real.log (g1 (e t).1)) ≤ sSup {((g1 s)^x * (g2 s)) | s : ℝ} := by
    intro t
    obtain ⟨s, u⟩ := e t
    simp only
    have hc : 0 < (g1 s)^u * g2 s := mul_pos (Real.rpow_pos_of_pos (pos1 s) u) (pos2 s)
    have h3 : (g1 s)^x * g2 s = (g1 s)^u * g2 s * Real.exp (Real.log (g1 s) * (x - u)) := by
      rw [← Real.rpow_def_of_pos (pos1 s), show x = u + (x - u) by ring]
      simp only [add_sub_cancel_left]
      rw [Real.rpow_add (pos1 s)]; ring
    have h4 := Real.add_one_le_exp (Real.log (g1 s) * (x - u))
    have h5 : (g1 s)^x * g2 s ≤ sSup {((g1 s)^x * (g2 s)) | s : ℝ} := le_csSup bdd ⟨s, rfl⟩
    have h6 := mul_le_mul_of_nonneg_left h4 hc.le
    nlinarith
  have hne : {(x * ((g1 (e t).1)^(e t).2 * g2 (e t).1 * Real.log (g1 (e t).1)) + (g1 (e t).1)^(e t).2 * g2 (e t).1 * (1 - (e t).2 * Real.log (g1 (e t).1))) | t : ℝ}.Nonempty := ⟨_, 0, rfl⟩
  have bdd2 : BddAbove {(x * ((g1 (e t).1)^(e t).2 * g2 (e t).1 * Real.log (g1 (e t).1)) + (g1 (e t).1)^(e t).2 * g2 (e t).1 * (1 - (e t).2 * Real.log (g1 (e t).1))) | t : ℝ} := by
    refine ⟨sSup {((g1 s)^x * (g2 s)) | s : ℝ}, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact key t
  apply le_antisymm
  · refine csSup_le ⟨g1 0 ^ x * g2 0, 0, rfl⟩ ?_
    rintro _ ⟨s, rfl⟩
    apply le_csSup bdd2
    refine ⟨e.symm (s, x), ?_⟩
    simp only [Equiv.apply_symm_apply]
    ring
  · exact csSup_le hne (by rintro _ ⟨t, rfl⟩; exact key t)
