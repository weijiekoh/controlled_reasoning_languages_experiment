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
  have hla : ∀ s, 0 ≤ Real.log (g1 s) := fun s => Real.log_nonneg (hgim s).1
  have hA : ∀ s, Real.log (g1 s) ≤ Real.log B1 := fun s => Real.log_le_log (hpos1 s) (hB s).1
  have hC : ∀ s, Real.log (g2 s) ≤ Real.log B2 := fun s => Real.log_le_log (hpos2 s) (hB s).2
  have hE : ∀ x s, g1 s ^ x * g2 s = Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
    intro x s
    rw [Real.exp_add, Real.exp_log (hpos2 s), Real.rpow_def_of_pos (hpos1 s)]
    ring_nf
  have hbdd : ∀ x : ℝ, BddAbove {y | ∃ s, g1 s ^ x * g2 s = y} := by
    intro x
    refine ⟨Real.exp (|x| * Real.log B1 + Real.log B2), ?_⟩
    rintro _ ⟨s, rfl⟩
    rw [hE]
    apply Real.exp_le_exp.2
    have h1 : x * Real.log (g1 s) ≤ |x| * Real.log (g1 s) :=
      mul_le_mul_of_nonneg_right (le_abs_self x) (hla s)
    have h2 : |x| * Real.log (g1 s) ≤ |x| * Real.log B1 :=
      mul_le_mul_of_nonneg_left (hA s) (abs_nonneg x)
    linarith [hC s]
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ x, F x = sSup {y | ∃ s, g1 s ^ x * g2 s = y} :=
    ⟨_, fun x => rfl⟩
  have hsup : ∀ x s, g1 s ^ x * g2 s ≤ F x := fun x s => by
    rw [hF]; exact le_csSup (hbdd x) ⟨s, rfl⟩
  have hconv : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rw [hF (a * u + b * v)]
    refine csSup_le ⟨g1 0 ^ (a * u + b * v) * g2 0, 0, rfl⟩ ?_
    rintro _ ⟨s, rfl⟩
    have e : g1 s ^ (a * u + b * v) * g2 s
        = Real.exp (a * (u * Real.log (g1 s) + Real.log (g2 s))
            + b * (v * Real.log (g1 s) + Real.log (g2 s))) := by
      rw [hE]
      congr 1
      linear_combination (-Real.log (g2 s)) * hab
    have hc := convexOn_exp.2 (Set.mem_univ (u * Real.log (g1 s) + Real.log (g2 s)))
      (Set.mem_univ (v * Real.log (g1 s) + Real.log (g2 s))) ha hb hab
    simp only [smul_eq_mul] at hc
    have hu := hsup u s
    have hv := hsup v s
    rw [hE] at hu hv
    rw [e]
    have := mul_le_mul_of_nonneg_left hu ha
    have := mul_le_mul_of_nonneg_left hv hb
    linarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ t, m t = sInf {q | ∃ z, t < z ∧ q = (F z - F t) / (z - t)} :=
    ⟨_, fun t => rfl⟩
  have hbelow : ∀ t z, t < z → (F (t - 1) - F t) / ((t - 1) - t) ≤ (F z - F t) / (z - t) :=
    fun t z hz => hconv.secant_mono (Set.mem_univ t) (Set.mem_univ (t - 1)) (Set.mem_univ z)
      (by intro h; linarith) (by intro h; linarith) (by linarith)
  have hsubg : ∀ t x, F t + m t * (x - t) ≤ F x := by
    intro t x
    rcases lt_trichotomy x t with h | h | h
    · have hle : (F t - F x) / (t - x) ≤ m t := by
        rw [hm t]
        refine le_csInf ⟨(F (t + 1) - F t) / (t + 1 - t), t + 1, by linarith, rfl⟩ ?_
        rintro _ ⟨z, hz, rfl⟩
        exact hconv.slope_mono_adjacent (Set.mem_univ x) (Set.mem_univ z) h hz
      rw [div_le_iff₀ (by linarith)] at hle
      have e : m t * (x - t) = -(m t * (t - x)) := by ring
      linarith
    · subst h; simp
    · have hge : m t ≤ (F x - F t) / (x - t) := by
        rw [hm t]
        refine csInf_le ⟨(F (t - 1) - F t) / ((t - 1) - t), ?_⟩ ⟨x, h, rfl⟩
        rintro _ ⟨z, hz, rfl⟩
        exact hbelow t z hz
      rw [le_div_iff₀ (by linarith)] at hge
      linarith
  refine ⟨fun t => m t, fun t => F t - m t * t, fun x => ?_⟩
  rw [← hF x]
  have hup : ∀ t, x * m t + (F t - m t * t) ≤ F x := fun t => by
    have e : x * m t + (F t - m t * t) = F t + m t * (x - t) := by ring
    have := hsubg t x
    linarith
  have hbT : BddAbove {y | ∃ t, x * m t + (F t - m t * t) = y} := by
    refine ⟨F x, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hup t
  apply le_antisymm
  · exact le_csSup hbT ⟨x, by ring⟩
  · refine csSup_le ⟨x * m x + (F x - m x * x), x, rfl⟩ ?_
    rintro _ ⟨t, rfl⟩
    exact hup t
