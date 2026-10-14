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
  have hp1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hp2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have hrw : ∀ x s, g1 s ^ x * g2 s = Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
    intro x s
    rw [Real.rpow_def_of_pos (hp1 s), Real.exp_add, Real.exp_log (hp2 s), mul_comm (Real.log (g1 s)) x]
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ x, F x = sSup {y | ∃ s : ℝ, g1 s ^ x * g2 s = y} :=
    ⟨_, fun _ => rfl⟩
  have hbd : ∀ x s, g1 s ^ x * g2 s ≤ Real.exp (|x| * Real.log B1 + Real.log B2) := by
    intro x s
    rw [hrw]
    apply Real.exp_le_exp.mpr
    have ha0 : 0 ≤ Real.log (g1 s) := Real.log_nonneg (hgim s).1
    have hb0 : 0 ≤ Real.log (g2 s) := Real.log_nonneg (hgim s).2
    have haA : Real.log (g1 s) ≤ Real.log B1 :=
      Real.log_le_log (hp1 s) (hB s).1
    have hbC : Real.log (g2 s) ≤ Real.log B2 :=
      Real.log_le_log (hp2 s) (hB s).2
    have h1 : x * Real.log (g1 s) ≤ |x| * Real.log (g1 s) :=
      mul_le_mul_of_nonneg_right (le_abs_self x) ha0
    have h2 : |x| * Real.log (g1 s) ≤ |x| * Real.log B1 :=
      mul_le_mul_of_nonneg_left haA (abs_nonneg x)
    linarith
  have hbdd : ∀ x : ℝ, BddAbove {y | ∃ s : ℝ, g1 s ^ x * g2 s = y} := by
    intro x
    refine ⟨Real.exp (|x| * Real.log B1 + Real.log B2), ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hbd x s
  have hne : ∀ x : ℝ, {y | ∃ s : ℝ, g1 s ^ x * g2 s = y}.Nonempty := fun x => ⟨g1 0 ^ x * g2 0, 0, rfl⟩
  have hle : ∀ x s, g1 s ^ x * g2 s ≤ F x := by
    intro x s
    rw [hF x]
    exact le_csSup (hbdd x) ⟨s, rfl⟩
  have hconv : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rw [hF (a * x + b * y)]
    apply csSup_le (hne _)
    rintro _ ⟨s, rfl⟩
    have hc := convexOn_exp.2 (Set.mem_univ (x * Real.log (g1 s) + Real.log (g2 s)))
      (Set.mem_univ (y * Real.log (g1 s) + Real.log (g2 s))) ha hb hab
    simp only [smul_eq_mul] at hc
    have e : a * (x * Real.log (g1 s) + Real.log (g2 s)) + b * (y * Real.log (g1 s) + Real.log (g2 s))
        = (a * x + b * y) * Real.log (g1 s) + Real.log (g2 s) := by
      have : b = 1 - a := by linarith
      subst this; ring
    rw [hrw, ← e]
    have h1 := hle x s
    rw [hrw] at h1
    have h2 := hle y s
    rw [hrw] at h2
    have := mul_le_mul_of_nonneg_left h1 ha
    have := mul_le_mul_of_nonneg_left h2 hb
    linarith [hc]
  -- subgradient
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ t, m t = sSup {q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)} :=
    ⟨_, fun _ => rfl⟩
  have hLbdd : ∀ t, BddAbove {q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)} := by
    intro t
    refine ⟨(F (t + 1) - F t) / (t + 1 - t), ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    have := hconv.slope_mono_adjacent (Set.mem_univ u) (Set.mem_univ (t + 1)) hu
      (by linarith : t < t + 1)
    simpa using this
  have hLne : ∀ t, {q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)}.Nonempty :=
    fun t => ⟨_, t - 1, by linarith, rfl⟩
  have hright : ∀ t v, t < v → m t ≤ (F v - F t) / (v - t) := by
    intro t v htv
    rw [hm t]
    apply csSup_le (hLne t)
    rintro _ ⟨u, hu, rfl⟩
    exact hconv.slope_mono_adjacent (Set.mem_univ u) (Set.mem_univ v) hu htv
  have hleft : ∀ t u, u < t → (F t - F u) / (t - u) ≤ m t := by
    intro t u hu
    rw [hm t]
    exact le_csSup (hLbdd t) ⟨u, hu, rfl⟩
  have supp : ∀ t x, F t + m t * (x - t) ≤ F x := by
    intro t x
    rcases lt_trichotomy x t with h | h | h
    · have := hleft t x h
      have hc : 0 < t - x := by linarith
      rw [div_le_iff₀ hc] at this
      nlinarith
    · subst h; simp
    · have := hright t x h
      have hc : 0 < x - t := by linarith
      rw [le_div_iff₀ hc] at this
      nlinarith
  refine ⟨m, fun t => F t - m t * t, fun x => ?_⟩
  rw [← hF x]
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, by ring⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  have := supp t x
  have e : x * m t + (F t - m t * t) = F t + m t * (x - t) := by ring
  rw [e]
  exact this
