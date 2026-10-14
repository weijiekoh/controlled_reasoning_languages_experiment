import Mathlib

open Filter Topology Set Nat

noncomputable abbrev putnam_2008_b5_solution : Set (ℝ → ℝ) := {fun (x : ℝ) => x + n | n : ℤ} ∪ {fun (x : ℝ) => -x + n | n : ℤ}
/--
Find all continuously differentiable functions f : \mathbb{R} \to \mathbb{R} such that for every rational number $q$, the number $f(q)$ is rational and has the same denominator as $q$.
-/
theorem putnam_2008_b5
(fqsat : (ℝ → ℝ) → ℚ → Prop)
(hfqsat : ∀ f q, fqsat f q ↔ ContDiff ℝ 1 f ∧ (∃ p : ℚ, p = f q ∧ p.den = q.den))
: ∀ f : (ℝ → ℝ), (∀ q : ℚ, fqsat f q) ↔ f ∈ putnam_2008_b5_solution :=by
  intro f
  have hnum : ∀ p : ℚ, (p:ℝ) * (p.den:ℝ) = (p.num:ℝ) := by
    intro p
    have h1 : (p.num:ℝ) / (p.den:ℝ) = (p:ℝ) := by exact_mod_cast Rat.num_div_den p
    have h2 : (p.den:ℝ) ≠ 0 := by positivity
    rw [← h1]; field_simp
  constructor
  · intro hall
    have hC : ContDiff ℝ 1 f := ((hfqsat f 0).1 (hall 0)).1
    have hden : ∀ q : ℚ, ∃ p : ℚ, (p:ℝ) = f q ∧ p.den = q.den :=
      fun q => ((hfqsat f q).1 (hall q)).2
    have hdiff : Differentiable ℝ f := hC.differentiable (by norm_num)
    have hcont : Continuous (deriv f) := hC.continuous_deriv (by norm_num)
    have hint : ∀ q : ℚ, ∃ K : ℤ, deriv f q = K := by
      intro q
      obtain ⟨p0, hp0f, hp0d⟩ := hden q
      have hm : f q * (q.den : ℝ) = (p0.num : ℝ) := by
        have := hnum p0
        rw [hp0d, hp0f] at this
        exact this
      let r : ℕ → ℚ := fun n => q + 1 / ((q.den:ℚ)^2 * ((n:ℚ)+1))
      have hqd : (q.den:ℚ) ≠ 0 := by positivity
      have hr_den : ∀ n : ℕ, (r n).den = q.den^2 * (n+1) := by
        intro n
        have hn1 : ((n:ℚ)+1) ≠ 0 := by positivity
        have hreq : r n = (((q.num * q.den * ((n:ℤ)+1) + 1 : ℤ)) : ℚ) / (((q.den:ℤ)^2 * ((n:ℤ)+1) : ℤ) : ℚ) := by
          simp only [r]
          push_cast
          rw [← Rat.mul_den_eq_num]
          field_simp
        have hpos : (0:ℤ) < (q.den:ℤ)^2 * ((n:ℤ)+1) := by positivity
        have hd1 : IsCoprime (q.num * q.den * ((n:ℤ)+1) + 1) (q.den:ℤ) :=
          ⟨1, -(q.num * ((n:ℤ)+1)), by ring⟩
        have hd2 : IsCoprime (q.num * q.den * ((n:ℤ)+1) + 1) ((n:ℤ)+1) :=
          ⟨1, -(q.num * q.den), by ring⟩
        have hcop := (hd1.pow_right (n := 2)).mul_right hd2
        have h := Rat.den_div_eq_of_coprime hpos (Int.isCoprime_iff_gcd_eq_one.mp hcop)
        rw [hreq]
        have h' : (((q.den:ℤ)^2 * ((n:ℤ)+1) : ℤ) : ℤ) = ((q.den^2 * (n+1) : ℕ) : ℤ) := by
          push_cast; ring
        have h'' := h
        rw [h'] at h''
        exact_mod_cast h''
      have hr_real : ∀ n : ℕ, ((r n : ℚ) : ℝ) = (q:ℝ) + 1 / ((q.den:ℝ)^2 * ((n:ℝ)+1)) := by
        intro n
        simp only [r]
        push_cast
        ring
      have hlim : Tendsto (fun n : ℕ => ((r n : ℚ) : ℝ)) atTop (𝓝[≠] (q:ℝ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have h1 : Tendsto (fun n : ℕ => (1 / (q.den:ℝ)^2) * (1 / ((n:ℝ)+1))) atTop (𝓝 0) := by
            have := (tendsto_const_nhds (x := 1 / (q.den:ℝ)^2)).mul tendsto_one_div_add_atTop_nhds_zero_nat
            rwa [mul_zero] at this
          have h2 := (tendsto_const_nhds (x := (q:ℝ))).add h1
          rw [add_zero] at h2
          refine h2.congr (fun n => ?_)
          rw [hr_real n, one_div_mul_one_div]
        · refine Eventually.of_forall (fun n => ?_)
          simp only [mem_compl_iff, mem_singleton_iff]
          intro h
          rw [hr_real n] at h
          have : (0:ℝ) < 1 / ((q.den:ℝ)^2 * ((n:ℝ)+1)) := by positivity
          linarith
      choose p hp using fun n => hden (r n)
      let U : ℕ → ℤ := fun n => (p n).num - p0.num * (q.den * ((n:ℤ)+1))
      have hslope : ∀ n : ℕ, slope f (q:ℝ) ((r n : ℚ) : ℝ) = ((U n : ℤ) : ℝ) := by
        intro n
        have hfr := hnum (p n)
        rw [(hp n).2, hr_den n] at hfr
        rw [(hp n).1] at hfr
        have hfr' : f ((r n : ℚ) : ℝ) * ((q.den:ℝ)^2 * ((n:ℝ)+1)) = ((p n).num : ℝ) := by
          push_cast at hfr; exact hfr
        have hxq : ((r n : ℚ) : ℝ) - (q:ℝ) = 1 / ((q.den:ℝ)^2 * ((n:ℝ)+1)) := by
          rw [hr_real n]; ring
        rw [slope_def_field, hxq]
        have hD : ((q.den:ℝ)^2 * ((n:ℝ)+1)) ≠ 0 := by positivity
        have hdq : (q.den:ℝ) ≠ 0 := by positivity
        have hn1 : ((n:ℝ)+1) ≠ 0 := by positivity
        simp only [U]
        push_cast at hfr ⊢
        have hfq : f q * q.den = p0.num := hm
        field_simp
        linear_combination hfr - ((q.den:ℝ) * ((n:ℝ)+1)) * hfq
      have hT : Tendsto (fun n : ℕ => slope f (q:ℝ) ((r n : ℚ) : ℝ)) atTop (𝓝 (deriv f q)) :=
        (hasDerivAt_iff_tendsto_slope.mp (hdiff q).hasDerivAt).comp hlim
      have hT' : Tendsto (fun n : ℕ => ((U n : ℤ) : ℝ)) atTop (𝓝 (deriv f q)) := by
        simpa [hslope] using hT
      have hmem := Int.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto hT'
        (Eventually.of_forall fun n => mem_range_self _)
      obtain ⟨K, hK⟩ := hmem
      exact ⟨K, hK.symm⟩
    have hallint : ∀ x : ℝ, ∃ K : ℤ, deriv f x = K := by
      have hS : IsClosed {x : ℝ | deriv f x ∈ range (Int.cast : ℤ → ℝ)} :=
        Int.isClosedEmbedding_coe_real.isClosed_range.preimage hcont
      have hQ : range (Rat.cast : ℚ → ℝ) ⊆ {x : ℝ | deriv f x ∈ range (Int.cast : ℤ → ℝ)} := by
        rintro _ ⟨q, rfl⟩
        obtain ⟨K, hK⟩ := hint q
        exact ⟨K, hK.symm⟩
      intro x
      have hx : x ∈ {x : ℝ | deriv f x ∈ range (Int.cast : ℤ → ℝ)} :=
        closure_minimal hQ hS (Rat.denseRange_cast x)
      obtain ⟨K, hK⟩ := hx
      exact ⟨K, hK.symm⟩
    have hc : ∀ x, deriv f x = deriv f 0 := by
      intro x
      obtain ⟨K1, h1⟩ := hallint 0
      obtain ⟨K2, h2⟩ := hallint x
      have hK12 : K1 = K2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have h' : K1 + 1 ≤ K2 := h
          have hmem : ((K1:ℝ) + 1/2) ∈ Icc (deriv f 0) (deriv f x) := by
            have : (K1:ℝ) + 1 ≤ K2 := by exact_mod_cast h'
            rw [h1, h2]; constructor <;> linarith
          obtain ⟨s, hs⟩ := intermediate_value_univ 0 x hcont hmem
          obtain ⟨K3, h3⟩ := hallint s
          have h4 : (2*K3 : ℤ) = 2*K1+1 := by
            have : (2*(K3:ℝ)) = 2*K1+1 := by linarith
            exact_mod_cast this
          omega
        · have h' : K2 + 1 ≤ K1 := h
          have hmem : ((K2:ℝ) + 1/2) ∈ Icc (deriv f x) (deriv f 0) := by
            have : (K2:ℝ) + 1 ≤ K1 := by exact_mod_cast h'
            rw [h1, h2]; constructor <;> linarith
          obtain ⟨s, hs⟩ := intermediate_value_univ x 0 hcont hmem
          obtain ⟨K3, h3⟩ := hallint s
          have h4 : (2*K3 : ℤ) = 2*K2+1 := by
            have : (2*(K3:ℝ)) = 2*K2+1 := by linarith
            exact_mod_cast this
          omega
      rw [h2, h1, hK12]
    have hlin : ∀ x, f x = deriv f 0 * x + f 0 := by
      have hdiff2 : Differentiable ℝ (fun y => f y - deriv f 0 * y) := fun x =>
        ((hdiff x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul (deriv f 0))).differentiableAt
      have hder : ∀ x, deriv (fun y => f y - deriv f 0 * y) x = 0 := by
        intro x
        have hd : HasDerivAt (fun y => f y - deriv f 0 * y) (deriv f x - deriv f 0 * 1) x :=
          (hdiff x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul (deriv f 0))
        rw [hd.deriv, hc x]; ring
      intro x
      have := is_const_of_deriv_eq_zero hdiff2 hder x 0
      simp only [mul_zero, sub_zero] at this
      linarith
    obtain ⟨p0, hp0f, hp0d⟩ := hden 0
    have hp0d' : p0.den = 1 := by rw [hp0d]; simp
    have hc0 : f 0 = ((p0.num : ℤ) : ℝ) := by
      have h := (Rat.den_eq_one_iff p0).mp hp0d'
      have h0' : ((0:ℚ):ℝ) = 0 := by simp
      rw [h0'] at hp0f
      rw [← hp0f]
      exact_mod_cast h.symm
    obtain ⟨K, hK⟩ := hallint 0
    have hlin' : ∀ x, f x = (K:ℝ) * x + (p0.num : ℝ) := by
      intro x
      rw [hlin x, hK, hc0]
    have hbad : ∀ N : ℕ, 2 ≤ N → ∀ M : ℤ, (K:ℝ) * (N:ℝ)⁻¹ + (p0.num : ℝ) = M → False := by
      intro N hN M hM
      have hden1 : ((N:ℚ)⁻¹).den = N := by
        rw [Rat.inv_natCast_den, if_neg (by omega)]
      obtain ⟨p, hp, hpd⟩ := hden ((N:ℚ)⁻¹)
      rw [hlin'] at hp
      push_cast at hp
      rw [hM] at hp
      have hpM : p = (M:ℚ) := by exact_mod_cast hp
      rw [hden1, hpM] at hpd
      simp at hpd
      omega
    have hK1 : K = 1 ∨ K = -1 := by
      by_cases h0 : K = 0
      · exfalso
        exact hbad 2 le_rfl (p0.num) (by simp [h0])
      by_contra hne
      obtain ⟨n1, n2⟩ := not_or.mp hne
      have hN : 2 ≤ K.natAbs := by omega
      have hne0 : ((K.natAbs:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rcases Int.natAbs_eq K with hk | hk
      · have hkR : (K:ℝ) = ((K.natAbs:ℕ):ℝ) := by
          have : (K:ℝ) = (((K.natAbs:ℕ):ℤ):ℝ) := congrArg (fun z : ℤ => (z:ℝ)) hk
          rw [this, Int.cast_natCast]
        refine hbad K.natAbs hN (1 + p0.num) ?_
        rw [hkR, mul_inv_cancel₀ hne0]
        push_cast; ring
      · have hkR : (K:ℝ) = -((K.natAbs:ℕ):ℝ) := by
          have : (K:ℝ) = Int.cast (-((K.natAbs:ℕ):ℤ)) := congrArg (fun z : ℤ => (z:ℝ)) hk
          rw [this, Int.cast_neg, Int.cast_natCast]
        refine hbad K.natAbs hN (p0.num - 1) ?_
        rw [hkR, neg_mul, mul_inv_cancel₀ hne0]
        push_cast; ring
    have hsol : f ∈ putnam_2008_b5_solution := by
      simp only [putnam_2008_b5_solution, Set.mem_union, Set.mem_setOf_eq]
      rcases hK1 with h | h
      · left
        refine ⟨p0.num, funext fun x => ?_⟩
        show x + ((p0.num:ℤ):ℝ) = f x
        rw [hlin' x, h]; push_cast; ring
      · right
        refine ⟨p0.num, funext fun x => ?_⟩
        show -x + ((p0.num:ℤ):ℝ) = f x
        rw [hlin' x, h]; push_cast; ring
    exact hsol
  · intro hmem q
    simp only [putnam_2008_b5_solution, Set.mem_union, Set.mem_setOf_eq] at hmem
    rw [hfqsat]
    rcases hmem with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · refine ⟨by fun_prop, (q + n : ℚ), ?_, Rat.add_intCast_den q n⟩
      simp
    · refine ⟨by fun_prop, (-q + n : ℚ), ?_, by rw [Rat.add_intCast_den, Rat.neg_den]⟩
      simp
