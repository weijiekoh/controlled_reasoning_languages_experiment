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
  obtain ⟨B1, B2, hB⟩ := hgbd
  have hpos1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hpos2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have ha0 : ∀ s, 0 ≤ Real.log (g1 s) := fun s => Real.log_nonneg (hgim s).1
  have hb0 : ∀ s, 0 ≤ Real.log (g2 s) := fun s => Real.log_nonneg (hgim s).2
  have hac : ∀ s, Real.log (g1 s) ≤ Real.log B1 := fun s => Real.log_le_log (hpos1 s) (hB s).1
  have hbc : ∀ s, Real.log (g2 s) ≤ Real.log B2 := fun s => Real.log_le_log (hpos2 s) (hB s).2
  have hc1 : 0 ≤ Real.log B1 := le_trans (ha0 0) (hac 0)
  have key : ∀ s x, g1 s ^ x * g2 s = Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
    intro s x
    rw [Real.rpow_def_of_pos (hpos1 s), Real.exp_add, Real.exp_log (hpos2 s),
      mul_comm (Real.log (g1 s)) x]
  have hbound : ∀ x s, x * Real.log (g1 s) + Real.log (g2 s) ≤ |x| * Real.log B1 + Real.log B2 := by
    intro x s
    have h1 : x * Real.log (g1 s) ≤ |x| * Real.log B1 := by
      nlinarith [mul_nonneg (sub_nonneg.2 (le_abs_self x)) (ha0 s),
        mul_nonneg (abs_nonneg x) (sub_nonneg.2 (hac s))]
    linarith [hbc s]
  have hA_bdd : ∀ x : ℝ, BddAbove {y | ∃ s, g1 s ^ x * g2 s = y} := by
    intro x
    refine ⟨Real.exp (|x| * Real.log B1 + Real.log B2), ?_⟩
    intro y hy
    obtain ⟨s, rfl⟩ := hy
    rw [key]
    exact Real.exp_le_exp.2 (hbound x s)
  have tang : ∀ s p x : ℝ, Real.exp (p * Real.log (g1 s) + Real.log (g2 s)) * (1 + Real.log (g1 s) * (x - p))
      ≤ Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
    intro s p x
    have h := Real.add_one_le_exp (Real.log (g1 s) * (x - p))
    have e2 : Real.exp (x * Real.log (g1 s) + Real.log (g2 s))
        = Real.exp (p * Real.log (g1 s) + Real.log (g2 s)) * Real.exp (Real.log (g1 s) * (x - p)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  obtain ⟨e⟩ : Nonempty (ℝ ≃ ℝ × ℝ) := by
    apply Cardinal.eq.1
    simp [Cardinal.mk_prod, Cardinal.mk_real, Cardinal.continuum_mul_self]
  refine ⟨fun t => Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * Real.log (g1 (e t).1),
    fun t => Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * (1 - Real.log (g1 (e t).1) * (e t).2), ?_⟩
  intro x
  have hBle : ∀ t : ℝ, x * (Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * Real.log (g1 (e t).1))
      + Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * (1 - Real.log (g1 (e t).1) * (e t).2)
      ≤ g1 (e t).1 ^ x * g2 (e t).1 := by
    intro t
    rw [key]
    have := tang (e t).1 (e t).2 x
    rw [mul_comm (e t).2] at this
    linarith [show x * (Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * Real.log (g1 (e t).1))
      + Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * (1 - Real.log (g1 (e t).1) * (e t).2)
      = Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * (1 + Real.log (g1 (e t).1) * (x - (e t).2)) by ring]
  have hB_bdd : BddAbove {y | ∃ t : ℝ, x * (Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * Real.log (g1 (e t).1))
      + Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * (1 - Real.log (g1 (e t).1) * (e t).2) = y} := by
    obtain ⟨M, hM⟩ := hA_bdd x
    refine ⟨M, ?_⟩
    rintro y ⟨t, rfl⟩
    exact le_trans (hBle t) (hM ⟨(e t).1, rfl⟩)
  have hA_sub : ∀ s : ℝ, g1 s ^ x * g2 s ∈ {y | ∃ t : ℝ, x * (Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * Real.log (g1 (e t).1))
      + Real.exp (Real.log (g1 (e t).1) * (e t).2 + Real.log (g2 (e t).1)) * (1 - Real.log (g1 (e t).1) * (e t).2) = y} := by
    intro s
    refine ⟨e.symm (s, x), ?_⟩
    have he : e (e.symm (s, x)) = (s, x) := by simp
    rw [he, key]
    simp only
    ring_nf
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, 0, rfl⟩
    · rintro y ⟨s, rfl⟩
      exact le_csSup_of_le hB_bdd (hA_sub s) le_rfl
  · apply csSup_le
    · exact ⟨_, (e.symm (0, x)), rfl⟩
    · rintro y ⟨t, rfl⟩
      exact le_trans (hBle t) (le_csSup (hA_bdd x) ⟨(e t).1, rfl⟩)
