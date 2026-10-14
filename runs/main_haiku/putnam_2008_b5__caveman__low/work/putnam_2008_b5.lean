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
  · intro hf
    have hC : ContDiff ℝ 1 f := ((hfqsat f 0).1 (hf 0)).1
    have hdiff : ∀ x : ℝ, DifferentiableAt ℝ f x := fun x =>
      (hC.differentiable (by norm_num)) x
    have hden : ∀ q : ℚ, ∃ p : ℚ, (p : ℝ) = f q ∧ p.den = q.den := fun q => by
      obtain ⟨p, hp, hd⟩ := ((hfqsat f q).1 (hf q)).2
      exact ⟨p, hp, hd⟩
    -- a rational with denominator dividing N times N is integer
    have L1 : ∀ (p : ℚ) (N : ℕ), p.den ∣ N → ∃ m : ℤ, (p : ℝ) * (N : ℝ) = m := by
      intro p N hN
      obtain ⟨t, ht⟩ := hN
      have h' : (p : ℝ) * (p.den : ℝ) = (p.num : ℝ) := by
        exact_mod_cast Rat.mul_den_eq_num p
      refine ⟨p.num * t, ?_⟩
      rw [ht]
      push_cast
      linear_combination (t : ℝ) * h'
    -- converse: p = m / N forces den ∣ N
    have L2 : ∀ (p : ℚ) (N : ℕ) (m : ℤ), p = (m : ℚ) / (N : ℚ) → p.den ∣ N := by
      intro p N m hp
      have hp' : p = Rat.divInt m (N : ℤ) := by
        rw [Rat.divInt_eq_div, hp]
        push_cast
        rfl
      have h1 : ((p.den : ℕ) : ℤ) ∣ (N : ℤ) := by
        rw [hp']
        exact Rat.den_dvd m N
      exact_mod_cast h1
    -- derivative at each rational is an integer
    have hderQ : ∀ q : ℚ, ∃ n : ℤ, deriv f (q : ℝ) = n := by
      intro q
      have hD : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      have hDR : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
      obtain ⟨N, hNdef⟩ : ∃ N : ℕ → ℕ, ∀ k, N k = q.den ^ 2 * (k + 1) :=
        ⟨_, fun k => rfl⟩
      obtain ⟨y, hydef⟩ : ∃ y : ℕ → ℚ, ∀ k, y k = q + 1 / ((N k : ℕ) : ℚ) :=
        ⟨_, fun k => rfl⟩
      have hq : q * (q.den : ℚ) = q.num := Rat.mul_den_eq_num q
      have hy : ∀ k, y k = ((q.num * ((q.den : ℤ) * ((k : ℤ) + 1)) + 1 : ℤ) : ℚ)
          / ((N k : ℕ) : ℚ) := by
        intro k
        have hN' : ((N k : ℕ) : ℚ) ≠ 0 := by
          rw [hNdef k]
          push_cast
          exact mul_ne_zero (pow_ne_zero 2 hD) (by positivity)
        rw [hydef k, eq_div_iff hN', add_mul, one_div, inv_mul_cancel₀ hN']
        rw [hNdef k]
        push_cast
        linear_combination ((q.den : ℚ) * ((k : ℚ) + 1)) * hq
      have hdqN : ∀ k, q.den ∣ N k := fun k => ⟨q.den * (k + 1), by rw [hNdef k]; ring⟩
      have hT : Tendsto (fun k : ℕ => 1 / ((N k : ℕ) : ℝ)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (1 / ((q.den : ℝ) ^ 2))
        rw [mul_zero] at this
        refine Tendsto.congr (fun k => ?_) this
        rw [hNdef k]
        push_cast
        field_simp
      have hyR : ∀ k, ((y k : ℚ) : ℝ) - (q : ℝ) = 1 / ((N k : ℕ) : ℝ) := by
        intro k
        rw [hydef k]
        push_cast
        ring
      have ht : Tendsto (fun k => ((y k : ℚ) : ℝ)) atTop (𝓝[≠] (q : ℝ)) := by
        rw [tendsto_nhdsWithin_iff]
        constructor
        · have h1 : Tendsto (fun k => (q : ℝ) + 1 / ((N k : ℕ) : ℝ)) atTop (𝓝 ((q : ℝ) + 0)) :=
            tendsto_const_nhds.add hT
          rw [add_zero] at h1
          refine h1.congr (fun k => ?_)
          rw [← hyR k]
          ring
        · refine Eventually.of_forall (fun k => ?_)
          have h2 := hyR k
          have hpos : (0 : ℝ) < 1 / ((N k : ℕ) : ℝ) := by
            rw [hNdef k]
            push_cast
            positivity
          intro h
          have h' : ((y k : ℚ) : ℝ) = (q : ℝ) := h
          linarith
      have hslope := (hasDerivAt_iff_tendsto_slope.1 (hdiff (q : ℝ)).hasDerivAt).comp ht
      obtain ⟨pq, hpq, hdpq⟩ := hden q
      have hZ : ∀ k, ∃ Z : ℤ, slope f (q : ℝ) ((y k : ℚ) : ℝ) = Z := by
        intro k
        obtain ⟨py, hpy, hdy⟩ := hden (y k)
        obtain ⟨m1, hm1⟩ := L1 py (N k) (by
          rw [hdy]; exact L2 (y k) (N k) _ (hy k))
        obtain ⟨m2, hm2⟩ := L1 pq (N k) (by rw [hdpq]; exact hdqN k)
        refine ⟨m1 - m2, ?_⟩
        rw [slope_def_field, hyR k, ← hpy, ← hpq, div_div_eq_mul_div, div_one]
        push_cast
        linear_combination hm1 - hm2
      choose Z hZ using hZ
      have hlim : deriv f (q : ℝ) ∈ range (Int.cast : ℤ → ℝ) := by
        apply Int.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto hslope
        exact Eventually.of_forall (fun k => ⟨Z k, (hZ k).symm⟩)
      obtain ⟨n, hn⟩ := hlim
      exact ⟨n, hn.symm⟩
    -- derivative is integer everywhere (density + closedness)
    have hdense : ∀ x : ℝ, deriv f x ∈ range (Int.cast : ℤ → ℝ) := by
      have hcont : Continuous (deriv f) := hC.continuous_deriv (by norm_num)
      have hcl : IsClosed (deriv f ⁻¹' range (Int.cast : ℤ → ℝ)) :=
        Int.isClosedEmbedding_coe_real.isClosed_range.preimage hcont
      have hsub : range (Rat.cast : ℚ → ℝ) ⊆ deriv f ⁻¹' range (Int.cast : ℤ → ℝ) := by
        rintro _ ⟨q, rfl⟩
        obtain ⟨n, hn⟩ := hderQ q
        exact ⟨n, hn.symm⟩
      have hcl2 := closure_minimal hsub hcl
      intro x
      have hx : x ∈ closure (range (Rat.cast : ℚ → ℝ)) := by
        rw [(Rat.denseRange_cast (𝕜 := ℝ)).closure_range]
        trivial
      exact hcl2 hx
    have hhalf : ∀ k m : ℤ, (k : ℝ) ≠ (m : ℝ) - 1 / 2 ∧ (k : ℝ) ≠ (m : ℝ) + 1 / 2 := by
      intro k m
      constructor <;> intro h
      · have h3 : (2 * k : ℤ) = 2 * m - 1 := by
          exact_mod_cast (show 2 * (k : ℝ) = 2 * (m : ℝ) - 1 by linarith)
        omega
      · have h3 : (2 * k : ℤ) = 2 * m + 1 := by
          exact_mod_cast (show 2 * (k : ℝ) = 2 * (m : ℝ) + 1 by linarith)
        omega
    -- derivative is constant (intermediate value theorem)
    have hconst : ∀ x, deriv f x = deriv f 0 := by
      intro x
      by_contra hne
      obtain ⟨n, hn⟩ := hdense x
      obtain ⟨m, hm⟩ := hdense 0
      have hnm : n ≠ m := by
        rintro rfl
        apply hne
        rw [← hn, ← hm]
      have hcont : ContinuousOn (deriv f) (uIcc 0 x) :=
        (hC.continuous_deriv (by norm_num)).continuousOn
      rcases lt_or_gt_of_ne hnm with h | h
      · have hmem : (m : ℝ) - 1 / 2 ∈ uIcc (deriv f 0) (deriv f x) := by
          rw [← hm, ← hn]
          rw [Set.mem_uIcc]
          right
          have h' : n + 1 ≤ m := by omega
          have h'' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h'
          constructor <;> linarith
        obtain ⟨z, _, hzeq⟩ := intermediate_value_uIcc hcont hmem
        obtain ⟨k, hk⟩ := hdense z
        exact (hhalf k m).1 (by rw [hk, hzeq])
      · have hmem : (m : ℝ) + 1 / 2 ∈ uIcc (deriv f 0) (deriv f x) := by
          rw [← hm, ← hn]
          rw [Set.mem_uIcc]
          left
          have h' : m + 1 ≤ n := by omega
          have h'' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h'
          constructor <;> linarith
        obtain ⟨z, _, hzeq⟩ := intermediate_value_uIcc hcont hmem
        obtain ⟨k, hk⟩ := hdense z
        exact (hhalf k m).2 (by rw [hk, hzeq])
    obtain ⟨n0, hn0⟩ := hdense 0
    have hderiv : ∀ x, deriv f x = n0 := fun x => by
      rw [hconst x, ← hn0]
    -- f is linear
    have hlin : ∀ x, f x = n0 * x + f 0 := by
      have hF : ∀ x, HasDerivAt (fun y => f y - (n0 : ℝ) * y) 0 x := by
        intro x
        have h1 : HasDerivAt f (deriv f x) x := (hdiff x).hasDerivAt
        have h2 := (hasDerivAt_id x).const_mul (n0 : ℝ)
        have h3 := h1.sub h2
        rw [hderiv x, mul_one, sub_self] at h3
        exact h3
      intro x
      have := is_const_of_deriv_eq_zero (f := fun y => f y - (n0 : ℝ) * y)
        (fun x => (hF x).differentiableAt) (fun x => (hF x).deriv) x 0
      simp only [mul_zero, sub_zero] at this
      linarith
    -- f 0 is integer
    obtain ⟨p0, hp0, hd0⟩ := hden 0
    obtain ⟨d, hd⟩ := L1 p0 1 (by rw [hd0]; simp)
    have hf0 : f 0 = d := by
      have h0 : ((0 : ℚ) : ℝ) = 0 := by simp
      rw [h0] at hp0
      rw [← hp0]
      push_cast at hd
      linarith
    -- if n0 = m * j with m ≥ 2, denominator contradiction at q = 1/m
    have hbad : ∀ m : ℕ, 2 ≤ m → ∀ j : ℤ, n0 = (m : ℤ) * j → False := by
      intro m hm j hj
      have hjR : (n0 : ℝ) = (m : ℝ) * (j : ℝ) := by exact_mod_cast hj
      have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      obtain ⟨p, hp, hpd⟩ := hden ((1 : ℚ) / (m : ℚ))
      have hfq : f (((1 : ℚ) / (m : ℚ) : ℚ) : ℝ) = (j : ℝ) + (d : ℝ) := by
        rw [hlin, hf0, hjR]
        push_cast
        field_simp
      have hpint : p = ((j + d : ℤ) : ℚ) := by
        have : (p : ℝ) = ((j + d : ℤ) : ℝ) := by
          rw [hp, hfq]
          norm_num
        exact_mod_cast this
      have hden1 : p.den = 1 := by
        rw [hpint]
        exact Rat.den_intCast _
      have hq : ((1 : ℚ) / (m : ℚ)).den = m := by
        rw [one_div, Rat.inv_natCast_den, if_neg (by omega)]
      rw [hq, hden1] at hpd
      omega
    have hn1 : n0 = 1 ∨ n0 = -1 := by
      by_cases h0 : n0 = 0
      · exact (hbad 2 (le_refl _) 0 (by simp [h0])).elim
      by_cases h1 : n0 ≥ 2
      · exact (hbad n0.toNat (by omega) 1
          (by rw [Int.toNat_of_nonneg (by omega)]; ring)).elim
      by_cases h2 : n0 ≤ -2
      · exact (hbad (-n0).toNat (by omega) (-1)
          (by rw [Int.toNat_of_nonneg (by omega)]; ring)).elim
      omega
    show f ∈ putnam_2008_b5_solution
    simp only [putnam_2008_b5_solution, Set.mem_union, Set.mem_setOf_eq]
    rcases hn1 with rfl | rfl
    · left
      exact ⟨d, funext fun x => by
        show x + (d : ℝ) = f x
        rw [hlin x, hf0]
        push_cast
        ring⟩
    · right
      exact ⟨d, funext fun x => by
        show -x + (d : ℝ) = f x
        rw [hlin x, hf0]
        push_cast
        ring⟩
  · intro hmem q
    simp only [putnam_2008_b5_solution, Set.mem_union, Set.mem_setOf_eq] at hmem
    rw [hfqsat]
    rcases hmem with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact ⟨by fun_prop, q + n, by simp, Rat.add_intCast_den q n⟩
    · refine ⟨by fun_prop, -q + n, by simp, ?_⟩
      rw [Rat.add_intCast_den, Rat.neg_den]
