import Mathlib

open Filter Topology Set Nat

noncomputable abbrev putnam_2008_b5_solution : Set (ℝ → ℝ) := {fun (x : ℝ) => x + n | n : ℤ} ∪ {fun (x : ℝ) => -x + n | n : ℤ}
/--
Find all continuously differentiable functions f : \mathbb{R} \to \mathbb{R} such that for every rational number $q$, the number $f(q)$ is rational and has the same denominator as $q$.
-/
theorem putnam_2008_b5
(fqsat : (ℝ → ℝ) → ℚ → Prop)
(hfqsat : ∀ f q, fqsat f q ↔ ContDiff ℝ 1 f ∧ (∃ p : ℚ, p = f q ∧ p.den = q.den))
: ∀ f : (ℝ → ℝ), (∀ q : ℚ, fqsat f q) ↔ f ∈ putnam_2008_b5_solution := by
  intro f
  constructor
  · intro hall
    have H : ∀ q : ℚ, ContDiff ℝ 1 f ∧ ∃ p : ℚ, (p : ℝ) = f (q : ℝ) ∧ p.den = q.den :=
      fun q => (hfqsat f q).1 (hall q)
    have hC : ContDiff ℝ 1 f := (H 0).1
    have hdiff : Differentiable ℝ f := hC.differentiable (by norm_num)
    have hderiv_cont : Continuous (deriv f) := hC.continuous_deriv (by norm_num)
    -- Step A: d * f(k/d) is an integer
    have hA : ∀ (d : ℕ) (k : ℤ), 0 < d → ∃ n : ℤ, f ((k : ℝ) / d) = n / d := by
      intro d k hd
      obtain ⟨_, p, hp, hpd⟩ := H ((k : ℚ) / (d : ℚ))
      have hdvd : ((k : ℚ) / (d : ℚ)).den ∣ d := by
        have h1 := Rat.den_dvd k (d : ℤ)
        rw [Rat.divInt_eq_div] at h1
        exact_mod_cast h1
      obtain ⟨t, ht⟩ := hdvd
      have hq : (((k : ℚ) / (d : ℚ) : ℚ) : ℝ) = (k : ℝ) / (d : ℝ) := by push_cast; ring
      rw [hq] at hp
      refine ⟨p.num * t, ?_⟩
      rw [← hp, Rat.cast_def, hpd]
      have hD0 : (((k : ℚ) / (d : ℚ)).den : ℝ) ≠ 0 := by exact_mod_cast (Rat.den_pos _).ne'
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h0
        have : (t : ℕ) = 0 := by exact_mod_cast h0
        rw [this, mul_zero] at ht
        omega
      have hdR : (d : ℝ) = ((k : ℚ) / (d : ℚ)).den * t := by exact_mod_cast ht
      rw [hdR]
      push_cast
      field_simp
    -- Step B: mean value on a grid cell
    have hB : ∀ (d : ℕ) (x : ℝ), 0 < d → ∃ c : ℝ, |c - x| ≤ 1 / (d : ℝ) ∧ ∃ n : ℤ, deriv f c = n := by
      intro d x hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
      set k : ℤ := ⌊(d : ℝ) * x⌋ with hk
      have hk1 : (k : ℝ) ≤ (d : ℝ) * x := Int.floor_le _
      have hk2 : (d : ℝ) * x < (k : ℝ) + 1 := Int.lt_floor_add_one _
      obtain ⟨n0, hn0⟩ := hA d k hd
      obtain ⟨n1, hn1⟩ := hA d (k + 1) hd
      have hab : (k : ℝ) / d < ((k + 1 : ℤ) : ℝ) / d := by
        apply div_lt_div_of_pos_right _ hdpos
        push_cast; linarith
      obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f hab hdiff.continuous.continuousOn
        (hdiff.differentiableOn)
      have hba : ((k + 1 : ℤ) : ℝ) / d = (k : ℝ) / d + 1 / d := by
        push_cast; try ring
      have hslope : (f (((k + 1 : ℤ) : ℝ) / d) - f ((k : ℝ) / d)) / (((k + 1 : ℤ) : ℝ) / d - (k : ℝ) / d)
          = ((n1 : ℝ) - n0) := by
        rw [hn0, hn1, hba]
        have : (k : ℝ) / d + 1 / d - (k : ℝ) / d = 1 / d := by ring
        rw [this]
        field_simp
      refine ⟨c, ?_, n1 - n0, ?_⟩
      · obtain ⟨hc1, hc2⟩ := hc
        have hxa : (k : ℝ) / d ≤ x := by
          rw [div_le_iff₀ hdpos]; linarith
        have hxb : x < ((k + 1 : ℤ) : ℝ) / d := by
          rw [lt_div_iff₀ hdpos]; push_cast at *; linarith
        rw [hba] at hc2 hxb
        rw [abs_le]
        constructor <;> linarith
      · rw [hcd, hslope]; push_cast; ring
    -- Step C: derivative is integer valued
    have hint : ∀ x : ℝ, ∃ n : ℤ, deriv f x = n := by
      intro x
      have hcl : IsClosed (Set.range (Int.cast : ℤ → ℝ)) := Int.isClosedEmbedding_coe_real.isClosed_range
      have hmem : deriv f x ∈ closure (Set.range (Int.cast : ℤ → ℝ)) := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.1 hderiv_cont.continuousAt ε hε
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
        obtain ⟨c, hc, n, hn⟩ := hB (N + 1) x (Nat.succ_pos N)
        have hN' : 1 / ((((N + 1 : ℕ)) : ℝ)) < δ := by push_cast; exact hN
        have hcd : dist c x < δ := by
          rw [Real.dist_eq]; exact lt_of_le_of_lt hc hN'
        have := hcont hcd
        refine ⟨(n : ℝ), ⟨n, rfl⟩, ?_⟩
        rw [hn, Real.dist_eq] at this
        rw [Real.dist_eq, abs_sub_comm]
        exact this
      rw [hcl.closure_eq] at hmem
      obtain ⟨n, hn⟩ := hmem
      exact ⟨n, hn.symm⟩
    -- Step D: derivative is constant
    have hhalf : ∀ (z : ℝ) (a : ℤ), deriv f z ≠ (a : ℝ) + 1 / 2 := by
      intro z a h
      obtain ⟨k, hk⟩ := hint z
      rw [hk] at h
      have h2 : ((2 * k : ℤ) : ℝ) = ((2 * a + 1 : ℤ) : ℝ) := by push_cast; linarith
      have h3 := Int.cast_injective h2
      omega
    have key : ∀ (x y : ℝ) (m n : ℤ), deriv f x = m → deriv f y = n → m = n := by
      intro x y m n hm hn
      by_contra hne
      have hIVT := intermediate_value_uIcc (a := x) (b := y) (f := deriv f) hderiv_cont.continuousOn
      rcases lt_or_gt_of_ne hne with h | h
      · have h' : (m : ℝ) + 1 ≤ n := by exact_mod_cast Int.add_one_le_of_lt h
        have ht : ((m : ℝ) + 1 / 2) ∈ Set.uIcc (deriv f x) (deriv f y) := by
          rw [hm, hn, Set.mem_uIcc]; left; constructor <;> linarith
        obtain ⟨z, _, hz⟩ := hIVT ht
        exact hhalf z m hz
      · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast Int.add_one_le_of_lt h
        have ht : ((n : ℝ) + 1 / 2) ∈ Set.uIcc (deriv f x) (deriv f y) := by
          rw [hm, hn, Set.mem_uIcc]; right; constructor <;> linarith
        obtain ⟨z, _, hz⟩ := hIVT ht
        exact hhalf z n hz
    obtain ⟨n0, hn0⟩ := hint 0
    have hfx : ∀ x, deriv f x = n0 := by
      intro x
      obtain ⟨m, hm⟩ := hint x
      rw [hm, key x 0 m n0 hm hn0]
    -- Step E: f is linear
    have hlin : ∀ x, f x = n0 * x + f 0 := by
      have hd : ∀ x, HasDerivAt (fun x => f x - (n0 : ℝ) * x) 0 x := by
        intro x
        have h1 := (hdiff x).hasDerivAt
        have h2 : HasDerivAt (fun x : ℝ => (n0 : ℝ) * x) ((n0 : ℝ) * 1) x :=
          (hasDerivAt_id x).const_mul _
        have h3 := h1.sub h2
        have hz : deriv f x - (n0 : ℝ) * 1 = 0 := by rw [hfx x]; ring
        rw [hz] at h3
        exact h3
      intro x
      have hc := is_const_of_deriv_eq_zero (f := fun x => f x - (n0 : ℝ) * x)
        (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) x 0
      simp only [mul_zero, sub_zero] at hc
      linarith
    -- Step F: f 0 is an integer
    obtain ⟨_, p0, hp0, hp0d⟩ := H 0
    have hp01 : p0.den = 1 := by rw [hp0d]; simp
    have hf0 : f 0 = (p0.num : ℝ) := by
      have : ((0 : ℚ) : ℝ) = 0 := by simp
      rw [this] at hp0
      rw [← hp0, ← Rat.coe_int_num_of_den_eq_one hp01]
      simp
    -- Step G: n0 = ±1
    have hn0pm : n0 = 1 ∨ n0 = -1 := by
      by_cases hz : n0 = 0
      · exfalso
        obtain ⟨_, p2, hp2, hp2d⟩ := H (1 / 2)
        have hq : ((1 / 2 : ℚ) : ℝ) = (1 / 2 : ℝ) := by push_cast; ring
        rw [hq, hlin, hz, hf0] at hp2
        simp at hp2
        have hp2c : p2 = (p0.num : ℚ) := by exact_mod_cast hp2
        rw [hp2c, Rat.den_intCast] at hp2d
        norm_num at hp2d
      · have hnR : (n0 : ℝ) ≠ 0 := by exact_mod_cast hz
        obtain ⟨_, p3, hp3, hp3d⟩ := H ((1 : ℚ) / (n0 : ℚ))
        have hq : (((1 : ℚ) / (n0 : ℚ) : ℚ) : ℝ) = 1 / (n0 : ℝ) := by push_cast; ring
        rw [hq, hlin, hf0] at hp3
        have hval : (n0 : ℝ) * (1 / (n0 : ℝ)) + (p0.num : ℝ) = ((1 + p0.num : ℤ) : ℝ) := by
          field_simp; push_cast; ring
        rw [hval] at hp3
        have hp3c : p3 = ((1 + p0.num : ℤ) : ℚ) := by exact_mod_cast hp3
        rw [hp3c, Rat.den_intCast] at hp3d
        have hqd : ((1 : ℚ) / (n0 : ℚ)).den = 1 := hp3d.symm
        have hqn := Rat.coe_int_num_of_den_eq_one hqd
        have hprod : (n0 : ℚ) * ((1 : ℚ) / (n0 : ℚ)).num = 1 := by
          rw [hqn]; field_simp
        have hprodZ : n0 * ((1 : ℚ) / (n0 : ℚ)).num = 1 := by exact_mod_cast hprod
        exact Int.eq_one_or_neg_one_of_mul_eq_one hprodZ
    -- Conclude
    simp only [putnam_2008_b5_solution, Set.mem_union, Set.mem_setOf_eq]
    rcases hn0pm with h | h
    · left
      refine ⟨p0.num, funext fun x => ?_⟩
      rw [hlin x, h, hf0]; push_cast; ring
    · right
      refine ⟨p0.num, funext fun x => ?_⟩
      rw [hlin x, h, hf0]; push_cast; ring
  · intro hmem q
    rw [hfqsat]
    simp only [putnam_2008_b5_solution, Set.mem_union, Set.mem_setOf_eq] at hmem
    rcases hmem with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · refine ⟨contDiff_id.add contDiff_const, q + n, ?_, Rat.add_intCast_den q n⟩
      push_cast; ring
    · refine ⟨contDiff_id.neg.add contDiff_const, -q + n, ?_, ?_⟩
      · push_cast; ring
      · rw [Rat.add_intCast_den, Rat.neg_den]
