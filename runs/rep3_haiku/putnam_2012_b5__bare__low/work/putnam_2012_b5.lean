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
  have hinj : Nonempty (ℝ × ℝ ↪ ℝ) := by
    have h : Cardinal.mk (ℝ × ℝ) ≤ Cardinal.mk ℝ := by
      rw [Cardinal.mk_prod, Cardinal.mk_real, Cardinal.lift_id, Cardinal.continuum_mul_self]
    exact (Cardinal.le_def _ _).mp h
  obtain ⟨e⟩ := hinj
  obtain ⟨pr, hprs⟩ : ∃ pr : ℝ → ℝ × ℝ, Function.Surjective pr :=
    ⟨Function.invFun e, Function.invFun_surjective e.injective⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℝ, ∀ s, a s = Real.log (g1 s) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, ∀ s, b s = Real.log (g2 s) := ⟨_, fun _ => rfl⟩
  have hp1 : ∀ s, 0 < g1 s := fun s => by linarith [(hgim s).1]
  have hp2 : ∀ s, 0 < g2 s := fun s => by linarith [(hgim s).2]
  have ha0 : ∀ s, 0 ≤ a s := fun s => by rw [ha]; exact Real.log_nonneg (hgim s).1
  have hb0 : ∀ s, 0 ≤ b s := fun s => by rw [hb]; exact Real.log_nonneg (hgim s).2
  have hA : ∀ s, a s ≤ Real.log B1 := fun s => by
    rw [ha]; exact Real.log_le_log (hp1 s) (hB s).1
  have hB2 : ∀ s, b s ≤ Real.log B2 := fun s => by
    rw [hb]; exact Real.log_le_log (hp2 s) (hB s).2
  have hkey : ∀ x s, g1 s ^ x * g2 s = Real.exp (x * a s + b s) := by
    intro x s
    calc g1 s ^ x * g2 s = Real.exp (Real.log (g1 s) * x) * Real.exp (Real.log (g2 s)) := by
          rw [Real.rpow_def_of_pos (hp1 s), Real.exp_log (hp2 s)]
      _ = Real.exp (x * a s + b s) := by
          rw [← Real.exp_add, ha, hb]; congr 1; ring
  have hbdd : ∀ x, BddAbove {y | ∃ s, Real.exp (x * a s + b s) = y} := by
    intro x
    refine ⟨Real.exp (|x| * Real.log B1 + Real.log B2), ?_⟩
    rintro y ⟨s, rfl⟩
    apply Real.exp_le_exp.mpr
    have h1 : x * a s ≤ |x| * Real.log B1 := by
      nlinarith [le_abs_self x, abs_nonneg x, ha0 s, hA s]
    linarith [hB2 s]
  obtain ⟨H1, hH1⟩ : ∃ H1 : ℝ × ℝ → ℝ, ∀ p, H1 p = a p.1 * Real.exp (a p.1 * p.2 + b p.1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨H2, hH2⟩ : ∃ H2 : ℝ × ℝ → ℝ, ∀ p, H2 p = Real.exp (a p.1 * p.2 + b p.1) * (1 - a p.1 * p.2) :=
    ⟨_, fun _ => rfl⟩
  refine ⟨fun t => H1 (pr t), fun t => H2 (pr t), ?_⟩
  have key : ∀ (p : ℝ × ℝ) (x : ℝ), x * H1 p + H2 p = Real.exp (a p.1 * p.2 + b p.1) * (1 + a p.1 * (x - p.2)) := by
    intro p x; rw [hH1, hH2]; ring
  have hEle : ∀ (p : ℝ × ℝ) (x : ℝ), Real.exp (a p.1 * p.2 + b p.1) * (1 + a p.1 * (x - p.2)) ≤ Real.exp (x * a p.1 + b p.1) := by
    intro p x
    have : Real.exp (x * a p.1 + b p.1) = Real.exp (a p.1 * p.2 + b p.1) * Real.exp (a p.1 * (x - p.2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a p.1 * (x - p.2))]) (Real.exp_pos _).le
  have hEself : ∀ s x, Real.exp (a s * x + b s) * (1 + a s * (x - x)) = Real.exp (x * a s + b s) := by
    intro s x; rw [sub_self, mul_zero, add_zero, mul_one]; congr 1; ring
  intro x
  have hLeq : {y | ∃ s, g1 s ^ x * g2 s = y} = {y | ∃ s, Real.exp (x * a s + b s) = y} := by
    ext y; simp only [Set.mem_setOf_eq, hkey]
  have hReq : {y | ∃ t, x * H1 (pr t) + H2 (pr t) = y} =
      {y | ∃ p : ℝ × ℝ, Real.exp (a p.1 * p.2 + b p.1) * (1 + a p.1 * (x - p.2)) = y} := by
    ext y; constructor
    · rintro ⟨t, rfl⟩; exact ⟨pr t, by rw [key]⟩
    · rintro ⟨p, rfl⟩
      obtain ⟨t, rfl⟩ := hprs p
      exact ⟨t, by rw [key]⟩
  beta_reduce
  rw [hLeq, hReq]
  have hRbdd : BddAbove {y | ∃ p : ℝ × ℝ, Real.exp (a p.1 * p.2 + b p.1) * (1 + a p.1 * (x - p.2)) = y} := by
    refine ⟨sSup {y | ∃ s, Real.exp (x * a s + b s) = y}, ?_⟩
    rintro y ⟨p, rfl⟩
    exact (hEle p x).trans (le_csSup (hbdd x) ⟨p.1, rfl⟩)
  have hLne : {y | ∃ s, Real.exp (x * a s + b s) = y}.Nonempty := ⟨_, 0, rfl⟩
  have hRne : {y | ∃ p : ℝ × ℝ, Real.exp (a p.1 * p.2 + b p.1) * (1 + a p.1 * (x - p.2)) = y}.Nonempty :=
    ⟨_, (0, 0), rfl⟩
  apply le_antisymm
  · apply csSup_le hLne
    rintro y ⟨s, rfl⟩
    rw [← hEself s x]
    exact le_csSup hRbdd ⟨(s, x), rfl⟩
  · apply csSup_le hRne
    rintro y ⟨p, rfl⟩
    exact (hEle p x).trans (le_csSup (hbdd x) ⟨p.1, rfl⟩)
