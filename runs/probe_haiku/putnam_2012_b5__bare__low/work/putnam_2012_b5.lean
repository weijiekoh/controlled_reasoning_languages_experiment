import Mathlib

open Matrix Function Real Topology Filter

/--
Prove that, for any two bounded functions $g_1, g_2: \RR \to [1, \infty)$, there exist functions $h_1, h_2: \RR \to \RR$ such that, for every $x \in \RR$, \[ \sup_{s \in \RR} (g_1(s)^x g_2(s))  = \max_{t \in \RR} (x h_1(t) + h_2(t)).\]
-/
theorem putnam_2012_b5
(g1 g2 : ℝ → ℝ)
(hgim : ∀ x : ℝ, g1 x ≥ 1 ∧ g2 x ≥ 1)
(hgbd : ∃ B1 B2 : ℝ, ∀ x : ℝ, g1 x ≤ B1 ∧ g2 x ≤ B2)
: ∃ h1 h2 : ℝ → ℝ, ∀ x : ℝ, sSup {((g1 s)^x * (g2 s)) | s : ℝ} = sSup {(x * (h1 t) + h2 t) | t : ℝ} :=by
  classical
  obtain ⟨e⟩ : Nonempty (ℝ ≃ ℝ × ℝ) := by
    rw [← Cardinal.eq]
    simp [Cardinal.mk_real, Cardinal.continuum_mul_self]
  obtain ⟨B1, B2, hB⟩ := hgbd
  have hB1 : 1 ≤ B1 := le_trans (hgim 0).1 (hB 0).1
  have hB2 : 1 ≤ B2 := le_trans (hgim 0).2 (hB 0).2
  -- tangent-line inequality
  have key : ∀ s u x : ℝ, g1 s ^ u * g2 s * (1 + Real.log (g1 s) * (x - u)) ≤ g1 s ^ x * g2 s := by
    intro s u x
    have hp : 0 < g1 s := by linarith [(hgim s).1]
    have hq : 0 < g2 s := by linarith [(hgim s).2]
    have e1 : g1 s ^ x = g1 s ^ u * Real.exp (Real.log (g1 s) * (x - u)) := by
      rw [← Real.rpow_def_of_pos hp, ← Real.rpow_add hp]
      congr 1; ring
    have h3 := Real.add_one_le_exp (Real.log (g1 s) * (x - u))
    have hV : 0 ≤ g1 s ^ u * g2 s := by positivity
    have := mul_le_mul_of_nonneg_left h3 hV
    rw [e1]
    linarith [this]
  -- uniform bound
  have bound : ∀ x : ℝ, ∃ C : ℝ, ∀ s, g1 s ^ x * g2 s ≤ C := by
    intro x
    refine ⟨B1 ^ |x| * B2, fun s => ?_⟩
    have hp : 0 < g1 s := by linarith [(hgim s).1]
    have hq : 0 < g2 s := by linarith [(hgim s).2]
    have h1 : g1 s ^ x ≤ B1 ^ |x| := by
      rcases le_total 0 x with hx | hx
      · calc g1 s ^ x ≤ B1 ^ x := Real.rpow_le_rpow hp.le (hB s).1 hx
          _ ≤ B1 ^ |x| := Real.rpow_le_rpow_of_exponent_le hB1 (le_abs_self x)
      · calc g1 s ^ x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hgim s).1 hx
          _ ≤ B1 ^ |x| := Real.one_le_rpow hB1 (abs_nonneg x)
    exact mul_le_mul h1 (hB s).2 hq.le (Real.rpow_nonneg (by linarith) _)
  obtain ⟨m, hm⟩ : ∃ m : ℝ × ℝ → ℝ, ∀ p, m p = Real.log (g1 p.1) * (g1 p.1 ^ p.2 * g2 p.1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ × ℝ → ℝ, ∀ p, c p = g1 p.1 ^ p.2 * g2 p.1 - p.2 * m p :=
    ⟨_, fun _ => rfl⟩
  have hlin : ∀ p : ℝ × ℝ, ∀ x : ℝ,
      x * m p + c p = (g1 p.1 ^ p.2 * g2 p.1) * (1 + Real.log (g1 p.1) * (x - p.2)) := by
    intro p x; rw [hc, hm]; ring
  refine ⟨fun t => m (e t), fun t => c (e t), fun x => ?_⟩
  beta_reduce
  have hsets : {x * m (e t) + c (e t) | t : ℝ} = {x * m p + c p | p : ℝ × ℝ} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨e t, rfl⟩
    · rintro ⟨p, rfl⟩; exact ⟨e.symm p, by simp⟩
  rw [hsets]
  have hlin_le : ∀ p : ℝ × ℝ, x * m p + c p ≤ g1 p.1 ^ x * g2 p.1 := by
    intro p; rw [hlin]; exact key p.1 p.2 x
  obtain ⟨C, hC⟩ := bound x
  have hAbdd : BddAbove {g1 s ^ x * g2 s | s : ℝ} := ⟨C, by rintro _ ⟨s, rfl⟩; exact hC s⟩
  have hBdd : BddAbove {x * m p + c p | p : ℝ × ℝ} := by
    refine ⟨C, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (hlin_le p).trans (hC p.1)
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨0, rfl⟩⟩
    · rintro _ ⟨s, rfl⟩
      have hmem : g1 s ^ x * g2 s ∈ {x * m p + c p | p : ℝ × ℝ} :=
        ⟨(s, x), by rw [hlin]; simp⟩
      exact le_csSup hBdd hmem
  · apply csSup_le
    · exact ⟨_, ⟨(0, 0), rfl⟩⟩
    · rintro _ ⟨p, rfl⟩
      exact (hlin_le p).trans (le_csSup hAbdd ⟨p.1, rfl⟩)
