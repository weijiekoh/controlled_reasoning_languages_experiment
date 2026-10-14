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
  classical
  obtain ⟨B1, B2, hB⟩ := hgbd
  have hpos1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hpos2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  let fs : ℝ → ℝ → ℝ := fun s x => Real.exp (Real.log (g1 s) * x + Real.log (g2 s))
  have hfs : ∀ s x, g1 s ^ x * g2 s = fs s x := by
    intro s x
    simp only [fs]
    rw [Real.rpow_def_of_pos (hpos1 s), Real.exp_add, Real.exp_log (hpos2 s)]
  have hF : ∀ x, sSup {y | ∃ s, g1 s ^ x * g2 s = y} = ⨆ s, fs s x := by
    intro x
    have : {y | ∃ s, g1 s ^ x * g2 s = y} = Set.range (fun s => fs s x) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_range, hfs]
    rw [this]
    rfl
  have hlog1 : ∀ s, 0 ≤ Real.log (g1 s) ∧ Real.log (g1 s) ≤ Real.log B1 := fun s =>
    ⟨Real.log_nonneg (hgim s).1, Real.log_le_log (hpos1 s) (hB s).1⟩
  have hlog2 : ∀ s, 0 ≤ Real.log (g2 s) ∧ Real.log (g2 s) ≤ Real.log B2 := fun s =>
    ⟨Real.log_nonneg (hgim s).2, Real.log_le_log (hpos2 s) (hB s).2⟩
  have hbdd : ∀ x, BddAbove (Set.range (fun s => fs s x)) := by
    intro x
    refine ⟨Real.exp (|x| * |Real.log B1| + |Real.log B2|), ?_⟩
    rintro _ ⟨s, rfl⟩
    apply Real.exp_le_exp.mpr
    have h1 := hlog1 s
    have h2 := hlog2 s
    have hM : Real.log (g1 s) * x ≤ |x| * |Real.log B1| := by
      have ha := le_abs_self (Real.log B1)
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        nlinarith
      · rw [abs_of_nonpos hx]
        nlinarith [abs_nonneg (Real.log B1)]
    have hb : Real.log (g2 s) ≤ |Real.log B2| := le_trans h2.2 (le_abs_self _)
    linarith
  have hconv : ConvexOn ℝ Set.univ (fun x => ⨆ s, fs s x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    apply ciSup_le
    intro s
    have e1 : fs s x ≤ ⨆ s, fs s x := le_ciSup (hbdd x) s
    have e2 : fs s y ≤ ⨆ s, fs s y := le_ciSup (hbdd y) s
    have key : fs s (a * x + b * y) ≤ a * fs s x + b * fs s y := by
      simp only [fs]
      have := convexOn_exp.2 (Set.mem_univ (Real.log (g1 s) * x + Real.log (g2 s)))
        (Set.mem_univ (Real.log (g1 s) * y + Real.log (g2 s))) ha hb hab
      simp only [smul_eq_mul] at this
      have eq : Real.log (g1 s) * (a * x + b * y) + Real.log (g2 s)
          = a * (Real.log (g1 s) * x + Real.log (g2 s)) + b * (Real.log (g1 s) * y + Real.log (g2 s)) := by
        linear_combination (-(Real.log (g2 s))) * hab
      rw [eq]
      exact this
    calc fs s (a * x + b * y) ≤ a * fs s x + b * fs s y := key
      _ ≤ a * (⨆ s, fs s x) + b * (⨆ s, fs s y) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 ha) (mul_le_mul_of_nonneg_left e2 hb)
  have hcont : ∀ s, Continuous (fs s) := fun s => by
    simp only [fs]; fun_prop
  have hlsc : LowerSemicontinuous (fun x => ⨆ s, fs s x) := by
    intro x y hy
    obtain ⟨s, hs⟩ := exists_lt_of_lt_ciSup hy
    filter_upwards [(continuousAt_const : ContinuousAt (fun _ : ℝ => y) x).eventually_lt
      (hcont s).continuousAt hs] with x' hx'
    exact lt_of_lt_of_le hx' (le_ciSup (hbdd x') s)
  obtain ⟨l, c, hle, hsup⟩ := ConvexOn.real_univ_sSup_of_nat_affine_eq hlsc hconv
  have hlin : ∀ i x, l i x = l i 1 * x := by
    intro i x
    have := (l i).map_smul x (1 : ℝ)
    simp only [smul_eq_mul, mul_one] at this
    rw [this, mul_comm]
  have hn : Function.Surjective (fun t : ℝ => ⌊|t|⌋₊) := by
    intro i
    exact ⟨(i : ℝ), by simp only [Nat.abs_cast, Nat.floor_natCast]⟩
  refine ⟨fun t => l ⌊|t|⌋₊ 1, fun t => c ⌊|t|⌋₊, fun x => ?_⟩
  rw [hF x]
  have hR : {y | ∃ t : ℝ, x * l ⌊|t|⌋₊ 1 + c ⌊|t|⌋₊ = y}
      = Set.range ((fun i : ℕ => (l i) x + c i) ∘ (fun t : ℝ => ⌊|t|⌋₊)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_range, Function.comp]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [hlin (⌊|t|⌋₊) x]; ring⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by rw [hlin (⌊|t|⌋₊) x]; ring⟩
  rw [hR, hn.range_comp]
  have hx : (⨆ i, (⇑(l i) + Function.const ℝ (c i))) x = ⨆ s, fs s x := by
    rw [hsup]
  rw [← hx, iSup_apply]
  rfl
