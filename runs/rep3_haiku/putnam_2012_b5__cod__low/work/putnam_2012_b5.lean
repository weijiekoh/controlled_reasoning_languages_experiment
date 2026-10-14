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
  have p1 : ∀ s, 0 < g1 s := fun s => by linarith [hgim s]
  have p2 : ∀ s, 0 < g2 s := fun s => by linarith [hgim s]
  have hrep : ∀ s z, g1 s ^ z * g2 s = Real.exp (z * Real.log (g1 s) + Real.log (g2 s)) := by
    intro s z
    rw [Real.rpow_def_of_pos (p1 s), Real.exp_add, Real.exp_log (p2 s), mul_comm (Real.log (g1 s)) z]
  have key : ∀ s x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      g1 s ^ (a * x + b * y) * g2 s ≤ a * (g1 s ^ x * g2 s) + b * (g1 s ^ y * g2 s) := by
    intro s x y a b ha hb hab
    simp only [hrep]
    have hc := convexOn_exp.2 (Set.mem_univ (x * Real.log (g1 s) + Real.log (g2 s)))
      (Set.mem_univ (y * Real.log (g1 s) + Real.log (g2 s))) ha hb hab
    simp only [smul_eq_mul] at hc
    have e : (a * x + b * y) * Real.log (g1 s) + Real.log (g2 s)
        = a * (x * Real.log (g1 s) + Real.log (g2 s)) + b * (y * Real.log (g1 s) + Real.log (g2 s)) := by
      linear_combination (-(Real.log (g2 s))) * hab
    rw [e]; exact hc
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ x : ℝ, F x = sSup {u | ∃ s, g1 s ^ x * g2 s = u} :=
    ⟨fun x => sSup {u | ∃ s, g1 s ^ x * g2 s = u}, fun x => rfl⟩
  have hbdd : ∀ x : ℝ, BddAbove {u | ∃ s, g1 s ^ x * g2 s = u} := by
    intro x
    refine ⟨Real.exp (|x| * Real.log B1 + Real.log B2), ?_⟩
    rintro u ⟨s, rfl⟩
    rw [hrep]
    apply Real.exp_le_exp.2
    have hL0 : 0 ≤ Real.log (g1 s) := Real.log_nonneg (hgim s).1
    have hL1 : Real.log (g1 s) ≤ Real.log B1 := Real.log_le_log (p1 s) (hB s).1
    have hB0 : 0 ≤ Real.log (g2 s) := Real.log_nonneg (hgim s).2
    have hB1' : Real.log (g2 s) ≤ Real.log B2 := Real.log_le_log (p2 s) (hB s).2
    have h1 : x * Real.log (g1 s) ≤ |x| * Real.log B1 :=
      le_trans (mul_le_mul_of_nonneg_right (le_abs_self x) hL0)
        (mul_le_mul_of_nonneg_left hL1 (abs_nonneg x))
    linarith
  have hFeq : ∀ (x : ℝ) (s : ℝ), g1 s ^ x * g2 s ≤ F x := fun x s => by
    rw [hF x]; exact le_csSup (hbdd x) ⟨s, rfl⟩
  have hFconv : ∀ x y a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → F (a * x + b * y) ≤ a * F x + b * F y := by
    intro x y a b ha hb hab
    rw [hF (a * x + b * y)]
    refine csSup_le ?_ ?_
    · exact ⟨_, 0, rfl⟩
    rintro u ⟨s, rfl⟩
    have h := key s x y a b ha hb hab
    nlinarith [mul_le_mul_of_nonneg_left (hFeq x s) ha, mul_le_mul_of_nonneg_left (hFeq y s) hb]
  have three : ∀ p q r : ℝ, q < p → p < r → (F p - F q) / (p - q) ≤ (F r - F p) / (r - p) := by
    intro p q r hqp hpr
    have hqr : 0 < r - q := by linarith
    have hne : r - q ≠ 0 := hqr.ne'
    have ha : (r - p) / (r - q) * (r - q) = r - p := div_mul_cancel₀ _ hne
    have hb : (p - q) / (r - q) * (r - q) = p - q := div_mul_cancel₀ _ hne
    have hc := hFconv q r ((r - p) / (r - q)) ((p - q) / (r - q))
      (div_nonneg (by linarith) hqr.le) (div_nonneg (by linarith) hqr.le)
      (by rw [← add_div, div_eq_one_iff_eq hne]; ring)
    have hm : ((r - p) / (r - q) * q + (p - q) / (r - q) * r) * (r - q) = p * (r - q) := by
      linear_combination q * ha + r * hb
    have e : (r - p) / (r - q) * q + (p - q) / (r - q) * r = p := mul_right_cancel₀ hne hm
    rw [e] at hc
    have h3 : (r - p) / (r - q) * (r - q) * F q = (r - p) * F q := by rw [ha]
    have h4 : (p - q) / (r - q) * (r - q) * F r = (p - q) * F r := by rw [hb]
    have hs : (r - q) * F p ≤ (r - p) * F q + (p - q) * F r := by
      nlinarith [mul_le_mul_of_nonneg_left hc hqr.le]
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hs]
  obtain ⟨c, hc⟩ : ∃ c : ℝ → ℝ, ∀ p, c p = sSup {u | ∃ q, q < p ∧ (F p - F q) / (p - q) = u} :=
    ⟨fun p => sSup {u | ∃ q, q < p ∧ (F p - F q) / (p - q) = u}, fun p => rfl⟩
  have cbdd : ∀ p : ℝ, BddAbove {u | ∃ q, q < p ∧ (F p - F q) / (p - q) = u} := by
    intro p
    refine ⟨(F (p + 1) - F p) / (p + 1 - p), ?_⟩
    rintro u ⟨q, hq, rfl⟩
    exact three p q (p + 1) hq (by linarith)
  have cle : ∀ p q, q < p → (F p - F q) / (p - q) ≤ c p := fun p q hq => by
    rw [hc p]; exact le_csSup (cbdd p) ⟨q, hq, rfl⟩
  have cge : ∀ p r, p < r → c p ≤ (F r - F p) / (r - p) := fun p r hr => by
    rw [hc p]
    refine csSup_le ⟨(F p - F (p - 1)) / (p - (p - 1)), p - 1, by linarith, rfl⟩ ?_
    rintro u ⟨q, hq, rfl⟩
    exact three p q r hq hr
  have hsub : ∀ p x, F p + c p * (x - p) ≤ F x := by
    intro p x
    rcases lt_trichotomy x p with h | h | h
    · have := cle p x h
      rw [div_le_iff₀ (by linarith)] at this
      nlinarith
    · subst h; simp
    · have := cge p x h
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith
  refine ⟨fun t => c t, fun t => F t - c t * t, fun x => ?_⟩
  rw [← hF x]
  show F x = sSup {u | ∃ t, x * c t + (F t - c t * t) = u}
  apply le_antisymm
  · have hb : BddAbove {u | ∃ t, x * c t + (F t - c t * t) = u} := by
      refine ⟨F x, ?_⟩
      rintro u ⟨t, rfl⟩
      have := hsub t x
      nlinarith
    refine le_csSup_of_le hb ⟨x, ?_⟩ le_rfl
    ring
  · refine csSup_le ?_ ?_
    · exact ⟨_, 0, rfl⟩
    rintro u ⟨t, rfl⟩
    have := hsub t x
    nlinarith
