import Mathlib

open Matrix Function Real Topology Filter

/--
Prove that, for any two bounded functions $g_1, g_2: \RR \to [1, \infty)$, there exist functions $h_1, h_2: \RR \to \RR$ such that, for every $x \in \RR$, \[ \sup_{s \in \RR} (g_1(s)^x g_2(s))  = \max_{t \in \RR} (x h_1(t) + h_2(t)).\]
-/
theorem putnam_2012_b5
(g1 g2 : ℝ → ℝ)
(hgim : ∀ x : ℝ, g1 x ≥ 1 ∧ g2 x ≥ 1)
(hgbd : ∃ B1 B2 : ℝ, ∀ x : ℝ, g1 x ≤ B1 ∧ g2 x ≤ B2)
: ∃ h1 h2 : ℝ → ℝ, ∀ x : ℝ, sSup {((g1 s)^x * (g2 s)) | s : ℝ} = sSup {(x * (h1 t) + h2 t) | t : ℝ} := by
  classical
  obtain ⟨B1, B2, hB⟩ := hgbd
  have hg1 : ∀ s, 0 < g1 s := fun s => lt_of_lt_of_le one_pos (hgim s).1
  have hg2 : ∀ s, 0 < g2 s := fun s => lt_of_lt_of_le one_pos (hgim s).2
  have ha0 : ∀ s, 0 ≤ Real.log (g1 s) := fun s => Real.log_nonneg (hgim s).1
  have ha1 : ∀ s, Real.log (g1 s) ≤ Real.log B1 := fun s =>
    Real.log_le_log (hg1 s) (hB s).1
  have hb1 : ∀ s, Real.log (g2 s) ≤ Real.log B2 := fun s =>
    Real.log_le_log (hg2 s) (hB s).2
  have key : ∀ (x : ℝ) (s : ℝ), g1 s ^ x * g2 s = Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
    intro x s
    rw [Real.rpow_def_of_pos (hg1 s), Real.exp_add, mul_comm x, Real.exp_log (hg2 s)]
  have key2 : ∀ y c : ℝ, Real.exp c * (1 + (y - c)) ≤ Real.exp y := by
    intro y c
    have h := Real.add_one_le_exp (y - c)
    have h2 := mul_le_mul_of_nonneg_left h (Real.exp_pos c).le
    have e1 : c + (y - c) = y := by ring
    rw [← Real.exp_add, e1] at h2
    have e2 : Real.exp c * (1 + (y - c)) = Real.exp c * (y - c + 1) := by ring
    rw [e2]; exact h2
  have hcard : Cardinal.mk ℝ = Cardinal.mk (ℝ × ℝ) := by
    simp [Cardinal.mk_real, Cardinal.mk_prod, Cardinal.continuum_mul_self]
  obtain ⟨e⟩ := Cardinal.eq.mp hcard
  refine ⟨fun t => Real.exp (e t).2 * Real.log (g1 (e t).1),
    fun t => Real.exp (e t).2 * (1 + Real.log (g2 (e t).1) - (e t).2), fun x => ?_⟩
  have hA : {(g1 s ^ x * g2 s) | s : ℝ} =
      {Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) | s : ℝ} := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, (key x s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, key x s⟩
  rw [hA]
  set U := Real.exp (|x| * Real.log B1 + Real.log B2) with hUdef
  have hU : ∀ s, Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) ≤ U := by
    intro s
    apply Real.exp_le_exp.mpr
    have h1 : x * Real.log (g1 s) ≤ |x| * Real.log B1 := by
      nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self x)) (ha0 s),
        mul_nonneg (abs_nonneg x) (sub_nonneg.2 (ha1 s))]
    linarith [hb1 s]
  have bddA : BddAbove {Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) | s : ℝ} := by
    refine ⟨U, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hU s
  have hBle : ∀ t : ℝ,
      x * (Real.exp (e t).2 * Real.log (g1 (e t).1))
        + Real.exp (e t).2 * (1 + Real.log (g2 (e t).1) - (e t).2)
        ≤ Real.exp (x * Real.log (g1 (e t).1) + Real.log (g2 (e t).1)) := by
    intro t
    have h := key2 (x * Real.log (g1 (e t).1) + Real.log (g2 (e t).1)) (e t).2
    have e3 : x * (Real.exp (e t).2 * Real.log (g1 (e t).1))
        + Real.exp (e t).2 * (1 + Real.log (g2 (e t).1) - (e t).2)
        = Real.exp (e t).2 * (1 + ((x * Real.log (g1 (e t).1) + Real.log (g2 (e t).1)) - (e t).2)) := by
      ring
    rw [e3]; exact h
  have bddB : BddAbove {x * (Real.exp (e t).2 * Real.log (g1 (e t).1))
      + Real.exp (e t).2 * (1 + Real.log (g2 (e t).1) - (e t).2) | t : ℝ} := by
    refine ⟨U, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact (hBle t).trans (hU (e t).1)
  apply le_antisymm
  · refine csSup_le ?_ ?_
    · exact ⟨_, 0, rfl⟩
    rintro _ ⟨s, rfl⟩
    have hv : x * (Real.exp (e (e.symm (s, x * Real.log (g1 s) + Real.log (g2 s)))).2
          * Real.log (g1 (e (e.symm (s, x * Real.log (g1 s) + Real.log (g2 s)))).1))
        + Real.exp (e (e.symm (s, x * Real.log (g1 s) + Real.log (g2 s)))).2
          * (1 + Real.log (g2 (e (e.symm (s, x * Real.log (g1 s) + Real.log (g2 s)))).1)
            - (e (e.symm (s, x * Real.log (g1 s) + Real.log (g2 s)))).2)
        = Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
      simp only [Equiv.apply_symm_apply]
      ring
    rw [← hv]
    exact le_csSup bddB ⟨e.symm (s, x * Real.log (g1 s) + Real.log (g2 s)), rfl⟩
  · refine csSup_le ?_ ?_
    · exact ⟨_, 0, rfl⟩
    rintro _ ⟨t, rfl⟩
    exact (hBle t).trans (le_csSup bddA ⟨(e t).1, rfl⟩)
