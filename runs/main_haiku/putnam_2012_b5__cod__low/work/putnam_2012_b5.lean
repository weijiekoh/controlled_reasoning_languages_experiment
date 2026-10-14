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
  have hg1p : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hg2p : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have ha0 : ∀ s, 0 ≤ Real.log (g1 s) := fun s => Real.log_nonneg (hgim s).1
  have hb0 : ∀ s, 0 ≤ Real.log (g2 s) := fun s => Real.log_nonneg (hgim s).2
  have hA : ∀ s, Real.log (g1 s) ≤ Real.log B1 :=
    fun s => Real.log_le_log (hg1p s) (hB s).1
  have hBb : ∀ s, Real.log (g2 s) ≤ Real.log B2 :=
    fun s => Real.log_le_log (hg2p s) (hB s).2
  have hrw : ∀ s x, g1 s ^ x * g2 s = Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) := by
    intro s x
    rw [Real.rpow_def_of_pos (hg1p s), Real.exp_add, mul_comm (Real.log (g1 s)) x, Real.exp_log (hg2p s)]
  have hL : ∀ x : ℝ, {z | ∃ s : ℝ, g1 s ^ x * g2 s = z}
      = {z | ∃ s : ℝ, Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) = z} := by
    intro x; simp only [hrw]
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ x, F x = sSup {z | ∃ s : ℝ, Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) = z} :=
    ⟨_, fun _ => rfl⟩
  have hbdd : ∀ x, BddAbove {z | ∃ s : ℝ, Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) = z} := by
    intro x
    refine ⟨Real.exp (|x| * Real.log B1 + Real.log B2), ?_⟩
    rintro z ⟨s, rfl⟩
    apply Real.exp_le_exp.2
    have h1 : x * Real.log (g1 s) ≤ |x| * Real.log (g1 s) :=
      mul_le_mul_of_nonneg_right (le_abs_self x) (ha0 s)
    have h2 : |x| * Real.log (g1 s) ≤ |x| * Real.log B1 :=
      mul_le_mul_of_nonneg_left (hA s) (abs_nonneg x)
    linarith [hBb s]
  have hFle : ∀ x s, Real.exp (x * Real.log (g1 s) + Real.log (g2 s)) ≤ F x := by
    intro x s
    rw [hF x]
    exact le_csSup (hbdd x) ⟨s, rfl⟩
  have hconv : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rw [hF (a * x + b * y)]
    apply csSup_le
    · exact ⟨_, 0, rfl⟩
    rintro z ⟨s, rfl⟩
    have e3 : Real.exp ((a * x + b * y) * Real.log (g1 s) + Real.log (g2 s))
        ≤ a * Real.exp (x * Real.log (g1 s) + Real.log (g2 s))
          + b * Real.exp (y * Real.log (g1 s) + Real.log (g2 s)) := by
      have := convexOn_exp.2 (Set.mem_univ (x * Real.log (g1 s) + Real.log (g2 s)))
        (Set.mem_univ (y * Real.log (g1 s) + Real.log (g2 s))) ha hb hab
      simp only [smul_eq_mul] at this
      have eq : (a * x + b * y) * Real.log (g1 s) + Real.log (g2 s)
          = a * (x * Real.log (g1 s) + Real.log (g2 s)) + b * (y * Real.log (g1 s) + Real.log (g2 s)) := by
        linear_combination (-(Real.log (g2 s))) * hab
      rw [eq]; exact this
    exact e3.trans (add_le_add (mul_le_mul_of_nonneg_left (hFle x s) ha)
      (mul_le_mul_of_nonneg_left (hFle y s) hb))
  -- slope monotonicity
  have hslope : ∀ y t z, y < t → t < z → (F t - F y) / (t - y) ≤ (F z - F t) / (z - t) :=
    fun y t z h1 h2 => hconv.slope_mono_adjacent (Set.mem_univ _) (Set.mem_univ _) h1 h2
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ, ∀ t, m t = sSup {q | ∃ y, y < t ∧ (F t - F y) / (t - y) = q} :=
    ⟨_, fun _ => rfl⟩
  have hmbdd : ∀ t, BddAbove {q | ∃ y, y < t ∧ (F t - F y) / (t - y) = q} := by
    intro t
    refine ⟨(F (t + 1) - F t) / (t + 1 - t), ?_⟩
    rintro q ⟨y, hy, rfl⟩
    exact hslope y t (t + 1) hy (by linarith)
  have hmle : ∀ t z, t < z → m t ≤ (F z - F t) / (z - t) := by
    intro t z hz
    rw [hm t]
    apply csSup_le
    · exact ⟨_, t - 1, by linarith, rfl⟩
    rintro q ⟨y, hy, rfl⟩
    exact hslope y t z hy hz
  have support : ∀ t z, F t + m t * (z - t) ≤ F z := by
    intro t z
    rcases lt_trichotomy z t with hzt | rfl | hzt
    · have hge : (F t - F z) / (t - z) ≤ m t := by
        rw [hm t]
        exact le_csSup (hmbdd t) ⟨z, hzt, rfl⟩
      have hpos : 0 < t - z := by linarith
      rw [div_le_iff₀ hpos] at hge
      nlinarith [hge]
    · simp
    · have h := hmle t z hzt
      have hpos : 0 < z - t := by linarith
      rw [le_div_iff₀ hpos] at h
      nlinarith [h]
  refine ⟨fun t => m t, fun t => F t - t * m t, fun x => ?_⟩
  rw [hL x, ← hF x]
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, by ring⟩, ?_⟩
  rintro z ⟨t, rfl⟩
  nlinarith [support t x]
