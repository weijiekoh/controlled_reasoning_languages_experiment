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
  have hpos1 : ∀ s : ℝ, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hpos2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have hterm : ∀ (s y : ℝ), g1 s ^ y * g2 s = exp (log (g1 s) * y + log (g2 s)) := by
    intro s y
    rw [Real.rpow_def_of_pos (hpos1 s), Real.exp_add, Real.exp_log (hpos2 s)]
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ y : ℝ, F y = sSup {v | ∃ s, g1 s ^ y * g2 s = v} :=
    ⟨fun (y : ℝ) => sSup {v | ∃ s, g1 s ^ y * g2 s = v}, fun (y : ℝ) => rfl⟩
  have hbdd : ∀ y : ℝ, BddAbove {v | ∃ s, g1 s ^ y * g2 s = v} := by
    intro y
    refine ⟨(B1 ^ y + 1) * B2, ?_⟩
    rintro v ⟨s, rfl⟩
    obtain ⟨h1, h2⟩ := hB s
    have hg1 : 1 ≤ g1 s := (hgim s).1
    have hg2 : 1 ≤ g2 s := (hgim s).2
    have hB1pos : 0 < B1 := by linarith
    have hBy : 0 < B1 ^ y := Real.rpow_pos_of_pos hB1pos y
    have hp : g1 s ^ y ≤ B1 ^ y + 1 := by
      rcases le_total 0 y with hy | hy
      · have := Real.rpow_le_rpow (by linarith) h1 hy
        linarith
      · have := Real.rpow_le_one_of_one_le_of_nonpos hg1 hy
        linarith
    exact mul_le_mul hp h2 (by linarith) (by linarith)
  have hle : ∀ (y : ℝ) (s : ℝ), g1 s ^ y * g2 s ≤ F y := by
    intro y s
    rw [hF y]
    exact le_csSup (hbdd y) ⟨s, rfl⟩
  have hF_le : ∀ (y M : ℝ), (∀ s, g1 s ^ y * g2 s ≤ M) → F y ≤ M := by
    intro y M h
    rw [hF y]
    refine csSup_le ⟨g1 0 ^ y * g2 0, 0, rfl⟩ ?_
    rintro v ⟨s, rfl⟩
    exact h s
  have hconv : ∀ u x l : ℝ, 0 ≤ l → l ≤ 1 → F (l * u + (1 - l) * x) ≤ l * F u + (1 - l) * F x := by
    intro u x l hl0 hl1
    apply hF_le
    intro s
    have hc := (convexOn_exp).2 (Set.mem_univ (log (g1 s) * u + log (g2 s)))
      (Set.mem_univ (log (g1 s) * x + log (g2 s))) hl0 (by linarith : (0:ℝ) ≤ 1 - l)
      (by ring)
    simp only [smul_eq_mul] at hc
    have h3 : log (g1 s) * (l * u + (1 - l) * x) + log (g2 s)
        = l * (log (g1 s) * u + log (g2 s)) + (1 - l) * (log (g1 s) * x + log (g2 s)) := by ring
    have key : g1 s ^ (l * u + (1 - l) * x) * g2 s ≤
        l * (g1 s ^ u * g2 s) + (1 - l) * (g1 s ^ x * g2 s) := by
      rw [hterm, hterm, hterm, h3]
      exact hc
    have a := mul_le_mul_of_nonneg_left (hle u s) hl0
    have b := mul_le_mul_of_nonneg_left (hle x s) (by linarith : (0:ℝ) ≤ 1 - l)
    linarith
  have h3pt : ∀ u t x : ℝ, u < t → t < x → (x - u) * F t ≤ (x - t) * F u + (t - u) * F x := by
    intro u t x hut htx
    have hxu : 0 < x - u := by linarith
    set l := (x - t) / (x - u) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith) hxu.le
    have hl1 : l ≤ 1 := (div_le_one hxu).2 (by linarith)
    have hpt : l * u + (1 - l) * x = t := by
      rw [hl]; field_simp; ring
    have hc := hconv u x l hl0 hl1
    rw [hpt] at hc
    have e : (x - u) * (l * F u + (1 - l) * F x) = (x - t) * F u + (t - u) * F x := by
      rw [hl]; field_simp; ring
    have := mul_le_mul_of_nonneg_left hc hxu.le
    linarith
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ t, m t = sSup {q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)} :=
    ⟨fun t => sSup {q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)}, fun t => rfl⟩
  have slope_le : ∀ u t x : ℝ, u < t → t < x → (F t - F u) / (t - u) ≤ (F x - F t) / (x - t) := by
    intro u t x hut htx
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have := h3pt u t x hut htx
    nlinarith
  have hQbdd : ∀ t, BddAbove {q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)} := by
    intro t
    refine ⟨(F (t + 1) - F t) / (t + 1 - t), ?_⟩
    rintro q ⟨u, hu, rfl⟩
    exact slope_le u t (t + 1) hu (by linarith)
  have hQne : ∀ t, ({q | ∃ u, u < t ∧ q = (F t - F u) / (t - u)} : Set ℝ).Nonempty := by
    intro t
    exact ⟨_, t - 1, by linarith, rfl⟩
  have up : ∀ t u, u < t → (F t - F u) / (t - u) ≤ m t := by
    intro t u hu
    rw [hm t]
    exact le_csSup (hQbdd t) ⟨u, hu, rfl⟩
  have lo : ∀ t x, t < x → m t ≤ (F x - F t) / (x - t) := by
    intro t x htx
    rw [hm t]
    apply csSup_le (hQne t)
    rintro q ⟨u, hu, rfl⟩
    exact slope_le u t x hu htx
  have line : ∀ t x, F t + m t * (x - t) ≤ F x := by
    intro t x
    rcases lt_trichotomy t x with htx | rfl | hxt
    · have := lo t x htx
      rw [le_div_iff₀ (by linarith)] at this
      linarith
    · simp
    · have := up t x hxt
      rw [div_le_iff₀ (by linarith)] at this
      linarith
  refine ⟨m, fun t => F t - m t * t, fun x => ?_⟩
  rw [← hF x]
  dsimp only
  apply le_antisymm
  · have hb : BddAbove {v | ∃ t, x * m t + (F t - m t * t) = v} := by
      refine ⟨F x, ?_⟩
      rintro v ⟨t, rfl⟩
      have := line t x
      linarith
    exact le_csSup hb ⟨x, by ring⟩
  · refine csSup_le ⟨_, x, rfl⟩ ?_
    rintro v ⟨t, rfl⟩
    have := line t x
    linarith
