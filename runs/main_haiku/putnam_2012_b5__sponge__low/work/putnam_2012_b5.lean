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
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ, ∀ x, F x = sSup {((g1 s)^x * (g2 s)) | s : ℝ} :=
    ⟨_, fun x => rfl⟩
  have hbdd : ∀ x : ℝ, BddAbove {((g1 s)^x * (g2 s)) | s : ℝ} := by
    intro x
    refine ⟨(max 1 B1)^|x| * B2, ?_⟩
    rintro v ⟨s, rfl⟩
    have hg1 := (hgim s).1
    have hg2 := (hgim s).2
    have hb1 := (hB s).1
    have hb2 := (hB s).2
    have hB2 : 0 ≤ B2 := by
      have := (hgim 0).2
      have := (hB 0).2
      linarith
    have hM : 1 ≤ max 1 B1 := le_max_left _ _
    have hg1M : g1 s ≤ max 1 B1 := le_trans hb1 (le_max_right _ _)
    have hpow : (g1 s)^x ≤ (max 1 B1)^|x| := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact Real.rpow_le_rpow (by linarith) hg1M hx
      · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos hg1 hx)
          (Real.one_le_rpow hM (abs_nonneg x))
    exact mul_le_mul hpow hb2 (by linarith) (Real.rpow_nonneg (le_trans zero_le_one hM) _)
  have le_F : ∀ x s, (g1 s)^x * (g2 s) ≤ F x := by
    intro x s
    rw [hFdef x]
    exact le_csSup (hbdd x) ⟨s, rfl⟩
  have F_le : ∀ x c, (∀ s, (g1 s)^x * (g2 s) ≤ c) → F x ≤ c := by
    intro x c hc
    rw [hFdef x]
    apply csSup_le
    · exact ⟨(g1 0)^x * (g2 0), 0, rfl⟩
    · rintro v ⟨s, rfl⟩
      exact hc s
  have hconv : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      F (a*x + b*y) ≤ a * F x + b * F y := by
    intro x y a b ha hb hab
    apply F_le
    intro s
    have hg1 : 0 < g1 s := by linarith [(hgim s).1]
    have hg2 : 0 < g2 s := by linarith [(hgim s).2]
    have hp1 : 0 ≤ (g1 s)^x * g2 s := by positivity
    have hp2 : 0 ≤ (g1 s)^y * g2 s := by positivity
    have hx' : ((g1 s)^x)^a = (g1 s)^(a*x) := by
      rw [← Real.rpow_mul hg1.le, mul_comm]
    have hy' : ((g1 s)^y)^b = (g1 s)^(b*y) := by
      rw [← Real.rpow_mul hg1.le, mul_comm]
    have h2 : (g2 s)^a * (g2 s)^b = g2 s := by
      rw [← Real.rpow_add hg2, hab, Real.rpow_one]
    have e : ((g1 s)^x * g2 s)^a * ((g1 s)^y * g2 s)^b = (g1 s)^(a*x+b*y) * g2 s := by
      rw [Real.mul_rpow (by positivity) hg2.le, Real.mul_rpow (by positivity) hg2.le, hx', hy']
      rw [show (g1 s)^(a*x) * (g2 s)^a * ((g1 s)^(b*y) * (g2 s)^b)
          = ((g1 s)^(a*x) * (g1 s)^(b*y)) * ((g2 s)^a * (g2 s)^b) by ring, h2,
          ← Real.rpow_add hg1]
    rw [← e]
    exact le_trans (Real.geom_mean_le_arith_mean2_weighted ha hb hp1 hp2 hab)
      (add_le_add (mul_le_mul_of_nonneg_left (le_F x s) ha)
        (mul_le_mul_of_nonneg_left (le_F y s) hb))
  have hcv : ConvexOn ℝ Set.univ F :=
    ⟨convex_univ, fun x _ y _ a b ha hb hab => by
      simpa [smul_eq_mul] using hconv x y a b ha hb hab⟩
  have hsl : ∀ y t z, y < t → t < z → (F t - F y)/(t-y) ≤ (F z - F t)/(z-t) :=
    fun y t z h1 h2 => hcv.slope_mono_adjacent (Set.mem_univ _) (Set.mem_univ _) h1 h2
  obtain ⟨h1, hh1⟩ : ∃ h1 : ℝ → ℝ, ∀ t, h1 t =
      sInf {v | ∃ u, t < u ∧ v = (F u - F t)/(u-t)} := ⟨_, fun t => rfl⟩
  have hbelow : ∀ t, ∀ v ∈ {v | ∃ u, t < u ∧ v = (F u - F t)/(u-t)},
      (F t - F (t-1))/(t-(t-1)) ≤ v := by
    rintro t v ⟨u, hu, rfl⟩
    exact hsl (t-1) t u (by linarith) hu
  have hle_h1 : ∀ t u, t < u → h1 t ≤ (F u - F t)/(u-t) := by
    intro t u hu
    rw [hh1 t]
    exact csInf_le ⟨_, hbelow t⟩ ⟨u, hu, rfl⟩
  have hge_h1 : ∀ t y, y < t → (F t - F y)/(t-y) ≤ h1 t := by
    intro t y hy
    rw [hh1 t]
    apply le_csInf
    · exact ⟨(F (t+1) - F t)/((t+1)-t), t+1, by linarith, rfl⟩
    · rintro v ⟨u, hu, rfl⟩
      exact hsl y t u hy hu
  have hsup : ∀ t y, F t + h1 t * (y - t) ≤ F y := by
    intro t y
    rcases lt_trichotomy y t with hy | hy | hy
    · have h := hge_h1 t y hy
      rw [div_le_iff₀ (by linarith)] at h
      have e : h1 t * (y - t) = -(h1 t * (t - y)) := by ring
      rw [e]
      linarith
    · subst hy
      simp
    · have h := hle_h1 t y hy
      rw [le_div_iff₀ (by linarith)] at h
      linarith
  refine ⟨h1, fun t => F t - t * h1 t, fun x => ?_⟩
  rw [← hFdef x]
  dsimp only
  refine (IsGreatest.csSup_eq ?_).symm
  refine ⟨⟨x, by ring⟩, ?_⟩
  rintro v ⟨t, rfl⟩
  have e : x * h1 t + (F t - t * h1 t) = F t + h1 t * (x - t) := by ring
  show x * h1 t + (F t - t * h1 t) ≤ F x
  rw [e]
  exact hsup t x
