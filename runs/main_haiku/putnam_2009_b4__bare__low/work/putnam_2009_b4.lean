import Mathlib

open intervalIntegral MvPolynomial Real

noncomputable abbrev putnam_2009_b4_solution : ℕ := 2020050
/--
Say that a polynomial with real coefficients in two variables, $x,y$, is \emph{balanced} if the average value of the polynomial on each circle centered at the origin is $0$. The balanced polynomials of degree at most $2009$ form a vector space $V$ over $\mathbb{R}$. Find the dimension of $V$.
-/
theorem putnam_2009_b4
    (IsBalanced : MvPolynomial (Fin 2) ℝ → Prop)
    (IsBalanced_def : ∀ P, IsBalanced P ↔ ∀ r > 0,
      (∫ t in (0 : ℝ)..(2 * π), eval ![r * cos t, r * sin t] P) / (2 * π * r) = 0)
    (V : Submodule ℝ (MvPolynomial (Fin 2) ℝ))
    (V_def : ∀ P, P ∈ V ↔ IsBalanced P ∧ P.totalDegree ≤ 2009) :
    Module.rank ℝ V = putnam_2009_b4_solution :=
  by
  classical
  -- Circle integrals of monomials
  obtain ⟨I, hI⟩ : ∃ I : ℕ → ℕ → ℝ, ∀ a b, I a b = ∫ t in (0:ℝ)..2*π, cos t ^ a * sin t ^ b :=
    ⟨_, fun _ _ => rfl⟩
  have hIodd : ∀ a b, (a % 2 = 1 ∨ b % 2 = 1) → I a b = 0 := by
    intro a b hab
    rw [hI]
    have hp : Function.Periodic (fun t : ℝ => cos t ^ a * sin t ^ b) (2*π) :=
      fun x => by simp [cos_add_two_pi, sin_add_two_pi]
    rcases hab with ha | hb
    · have ha' : Odd a := Nat.odd_iff.mpr ha
      have h1 := intervalIntegral.integral_comp_sub_left (fun t => cos t ^ a * sin t ^ b) (a := 0) (b := 2*π) π
      have h2 : ∀ x : ℝ, cos (π - x) ^ a * sin (π - x) ^ b = -(cos x ^ a * sin x ^ b) := by
        intro x; rw [cos_pi_sub, sin_pi_sub, ha'.neg_pow]; ring
      simp only [h2] at h1
      rw [intervalIntegral.integral_neg] at h1
      rw [show π - 2*π = -π by ring, show π - 0 = -π + 2*π by ring] at h1
      rw [hp.intervalIntegral_add_eq (-π) 0] at h1
      simp only [zero_add] at h1
      linarith
    · have hb' : Odd b := Nat.odd_iff.mpr hb
      have h1 := intervalIntegral.integral_comp_neg (fun t => cos t ^ a * sin t ^ b) (a := 0) (b := 2*π)
      have h2 : ∀ x : ℝ, cos (-x) ^ a * sin (-x) ^ b = -(cos x ^ a * sin x ^ b) := by
        intro x; rw [cos_neg, sin_neg, hb'.neg_pow]; ring
      simp only [h2] at h1
      rw [intervalIntegral.integral_neg] at h1
      have hh := hp.intervalIntegral_add_eq (-(2*π)) 0
      simp only [neg_zero, zero_add, neg_add_cancel] at hh h1
      rw [hh] at h1
      linarith
  have hpos : ∀ k : ℕ, 0 < I (2*k) 0 := by
    intro k
    rw [hI]
    simp only [pow_zero, mul_one]
    have hc : Continuous (fun t : ℝ => cos t ^ (2*k)) := by fun_prop
    have hp : Function.Periodic (fun t : ℝ => cos t ^ (2*k)) (2*π) := fun x => by simp [cos_add_two_pi]
    have e1 := hp.intervalIntegral_add_eq (-(π/2)) 0
    rw [show -(π/2) + 2*π = 3*π/2 by ring, zero_add] at e1
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := MeasureTheory.volume) (-(π/2)) (π/2)) (hc.intervalIntegrable (μ := MeasureTheory.volume) (π/2) (3*π/2))
    have h1 : 0 < ∫ t in (-(π/2))..(π/2), cos t ^ (2*k) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
        (fun x hx => pow_pos (cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩) _)
        (by linarith [pi_pos])
    have h2 : 0 ≤ ∫ t in (π/2)..(3*π/2), cos t ^ (2*k) :=
      intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun x _ => by rw [pow_mul]; positivity)
    linarith
  -- The index set of monomials of degree ≤ 2009
  have hgauss : ∀ n : ℕ, 2 * ∑ d ∈ Finset.range n, (d+1) = n * (n+1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  obtain ⟨T, hT, hTc⟩ : ∃ T : Finset (ℕ × ℕ), (∀ p, p ∈ T ↔ p.1 + p.2 ≤ 2009) ∧ T.card = 2021055 := by
    refine ⟨(Finset.range 2010).biUnion (fun d => Finset.HasAntidiagonal.antidiagonal d), fun p => ?_, ?_⟩
    · simp only [Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
      constructor
      · rintro ⟨a, ha, h⟩; omega
      · intro h; exact ⟨p.1 + p.2, by omega, rfl⟩
    · rw [Finset.card_biUnion (fun x _ y _ hxy => Finset.disjoint_left.mpr fun p hp hq => hxy (by
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq; omega))]
      simp only [Finset.Nat.card_antidiagonal]
      have := hgauss 2010
      omega
  -- Monomial exponents
  obtain ⟨mon, hmon⟩ : ∃ mon : ℕ × ℕ → (Fin 2 →₀ ℕ), ∀ p, mon p = Finsupp.equivFunOnFinite.symm ![p.1, p.2] :=
    ⟨_, fun _ => rfl⟩
  have hmon0 : ∀ p, mon p 0 = p.1 := by intro p; simp [hmon]
  have hmon1 : ∀ p, mon p 1 = p.2 := by intro p; simp [hmon]
  have hmon_inj : ∀ p q, mon p = mon q → p = q := fun p q h =>
    Prod.ext (by rw [← hmon0 p, ← hmon0 q, h]) (by rw [← hmon1 p, ← hmon1 q, h])
  have hmon_surj : ∀ m : Fin 2 →₀ ℕ, mon (m 0, m 1) = m := by
    intro m; ext i; fin_cases i <;> simp [hmon0, hmon1]
  -- The linear map from coefficient vectors to polynomials
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (↥T →₀ ℝ) →ₗ[ℝ] MvPolynomial (Fin 2) ℝ,
      ∀ c, Φ c = ∑ p : ↥T, c p • monomial (mon p.1) (1:ℝ) :=
    ⟨Finsupp.linearCombination ℝ (fun p : ↥T => monomial (mon p.1) (1:ℝ)), fun c => by
      rw [Finsupp.linearCombination_apply]
      exact Finsupp.sum_fintype c (fun (i : ↥T) (a : ℝ) => a • monomial (mon i.1) (1:ℝ)) (fun _ => zero_smul ℝ _)⟩
  have hΦinj : Function.Injective Φ := by
    have hli : LinearIndependent ℝ (fun p : ↥T => monomial (mon p.1) (1:ℝ)) := by
      have := (MvPolynomial.basisMonomials (Fin 2) ℝ).linearIndependent.comp
        (fun p : ↥T => mon p.1) (fun p q h => Subtype.ext (hmon_inj _ _ h))
      simpa [MvPolynomial.coe_basisMonomials, Function.comp_def] using this
    have hE : Φ = Finsupp.linearCombination ℝ (fun p : ↥T => monomial (mon p.1) (1:ℝ)) := by
      apply LinearMap.ext
      intro c
      rw [hΦ, Finsupp.linearCombination_apply]
      exact (Finsupp.sum_fintype c (fun (i : ↥T) (a : ℝ) => a • monomial (mon i.1) (1:ℝ)) (fun _ => zero_smul ℝ _)).symm
    rw [hE]
    unfold LinearIndependent at hli
    exact hli
  have hcoeff : ∀ c m, coeff m (Φ c) = ∑ p : ↥T, c p * (if mon p.1 = m then 1 else 0) := by
    intro c m
    rw [hΦ, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [MvPolynomial.coeff_smul, coeff_monomial]
    simp [smul_eq_mul]
  have hdeg : ∀ c m, 2009 < m 0 + m 1 → coeff m (Φ c) = 0 := by
    intro c m hm
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro p _
    have hp := (hT p.1).mp p.2
    have hne : mon p.1 ≠ m := fun h => by
      have h0 := hmon0 p.1
      have h1 := hmon1 p.1
      rw [h] at h0 h1
      omega
    simp [hne]
  have hdeg' : ∀ c m (hm : m 0 + m 1 ≤ 2009), coeff m (Φ c) = c ⟨(m 0, m 1), (hT _).mpr hm⟩ := by
    intro c m hm
    rw [hcoeff, Finset.sum_eq_single ⟨(m 0, m 1), (hT _).mpr hm⟩]
    · simp [hmon_surj]
    · intro p _ hp
      have hne : mon p.1 ≠ m := fun h => hp (Subtype.ext (Prod.ext (by rw [← hmon0 p.1, h]) (by rw [← hmon1 p.1, h])))
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hev : ∀ (x : Fin 2 → ℝ) (p : ℕ × ℕ), eval x (monomial (mon p) (1:ℝ)) = x 0 ^ p.1 * x 1 ^ p.2 := by
    intro x p
    simp [MvPolynomial.eval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, hmon0, hmon1]
  have hintegral : ∀ (c : ↥T →₀ ℝ) (r : ℝ), ∫ t in (0:ℝ)..2*π, eval ![r * cos t, r * sin t] (Φ c)
      = ∑ p : ↥T, (c p * I p.1.1 p.1.2) * r ^ (p.1.1 + p.1.2) := by
    intro c r
    have hfun : ∀ t, eval ![r * cos t, r * sin t] (Φ c)
        = ∑ p : ↥T, c p * (r ^ (p.1.1 + p.1.2) * (cos t ^ p.1.1 * sin t ^ p.1.2)) := by
      intro t
      rw [hΦ, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hev]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    simp_rw [hfun]
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro p _
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI]
      ring
    · intro p _
      apply Continuous.intervalIntegrable
      fun_prop
  -- Balanced condition as vanishing of a linear map G
  obtain ⟨G, hG⟩ : ∃ G : (↥T →₀ ℝ) →ₗ[ℝ] (Fin 1005 → ℝ),
      ∀ c k, G c k = ∑ p : ↥T, c p * (I p.1.1 p.1.2 * if p.1.1 + p.1.2 = 2 * (k:ℕ) then 1 else 0) :=
    ⟨Finsupp.linearCombination ℝ (fun p : ↥T => fun k : Fin 1005 =>
        I p.1.1 p.1.2 * if p.1.1 + p.1.2 = 2 * (k:ℕ) then 1 else 0), fun c k => by
      simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype, Finset.sum_apply]⟩
  have hbal : ∀ c, IsBalanced (Φ c) ↔ G c = 0 := by
    intro c
    rw [IsBalanced_def]
    obtain ⟨qc, hqc⟩ : ∃ q : Polynomial ℝ,
        q = ∑ p : ↥T, Polynomial.C (c p * I p.1.1 p.1.2) * Polynomial.X ^ (p.1.1 + p.1.2) := ⟨_, rfl⟩
    have hqe : ∀ r : ℝ, qc.eval r = ∑ p : ↥T, (c p * I p.1.1 p.1.2) * r ^ (p.1.1 + p.1.2) := by
      intro r
      rw [hqc, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp
    have hqcoeff : ∀ n, qc.coeff n = ∑ p : ↥T, if n = p.1.1 + p.1.2 then c p * I p.1.1 p.1.2 else 0 := by
      intro n
      rw [hqc, Polynomial.finsetSum_coeff]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Polynomial.coeff_C_mul_X_pow]
    have h2k : ∀ k : Fin 1005, G c k = qc.coeff (2 * (k:ℕ)) := by
      intro k
      rw [hqcoeff, hG]
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : p.1.1 + p.1.2 = 2 * (k:ℕ)
      · have h' : 2 * (k:ℕ) = p.1.1 + p.1.2 := h.symm
        rw [if_pos h, if_pos h']; ring
      · have h' : ¬ 2 * (k:ℕ) = p.1.1 + p.1.2 := fun e => h e.symm
        rw [if_neg h, if_neg h']; ring
    have step1 : (∀ r : ℝ, r > 0 → ∑ p : ↥T, (c p * I p.1.1 p.1.2) * r ^ (p.1.1 + p.1.2) = 0)
        ↔ qc = 0 := by
      constructor
      · intro h
        apply Polynomial.eq_zero_of_infinite_isRoot
        refine (Set.Ioi_infinite (0:ℝ)).mono ?_
        intro x hx
        show qc.eval x = 0
        rw [hqe]
        exact h x hx
      · intro h r _
        rw [← hqe, h, Polynomial.eval_zero]
    have step2 : qc = 0 ↔ G c = 0 := by
      constructor
      · intro h
        funext k
        rw [h2k k, h, Polynomial.coeff_zero]
        rfl
      · intro h
        ext n
        rw [Polynomial.coeff_zero]
        by_cases hodd : n % 2 = 1
        · rw [hqcoeff]
          apply Finset.sum_eq_zero
          intro p _
          split_ifs with hp
          · rw [hIodd p.1.1 p.1.2 (by omega)]; ring
          · rfl
        · by_cases hlt : n < 2010
          · have h4 : G c ⟨n / 2, by omega⟩ = qc.coeff n := by
              rw [h2k ⟨n / 2, by omega⟩]
              congr 1
              show 2 * (n / 2) = n
              omega
            rw [← h4]
            exact congrFun h _
          · rw [hqcoeff]
            apply Finset.sum_eq_zero
            intro p _
            have := (hT p.1).mp p.2
            rw [if_neg (by omega)]
    have hdiv : (∀ r > 0, (∫ t in (0:ℝ)..2*π, eval ![r * cos t, r * sin t] (Φ c)) / (2 * π * r) = 0)
        ↔ (∀ r : ℝ, r > 0 → ∑ p : ↥T, (c p * I p.1.1 p.1.2) * r ^ (p.1.1 + p.1.2) = 0) := by
      refine forall₂_congr fun r hr => ?_
      rw [hintegral, div_eq_zero_iff, or_iff_left (by positivity)]
    rw [hdiv, step1, step2]
  -- The balanced subspace is the image of the kernel of G
  have hrange : LinearMap.range G = ⊤ := by
    have hb : ∀ j : Fin 1005, (Pi.basisFun ℝ (Fin 1005)) j ∈ LinearMap.range G := by
      intro j
      have hI0 := (hpos j).ne'
      have hpj : (2 * (j:ℕ), 0) ∈ T := (hT _).mpr (by show 2 * (j:ℕ) + 0 ≤ 2009; have := j.isLt; omega)
      refine ⟨Finsupp.single (⟨(2 * (j:ℕ), 0), hpj⟩ : ↥T) (1 / I (2 * (j:ℕ)) 0), ?_⟩
      funext k
      rw [hG, Finset.sum_eq_single (⟨(2 * (j:ℕ), 0), hpj⟩ : ↥T)]
      · rw [Finsupp.single_eq_same, Pi.basisFun_apply]
        rcases eq_or_ne j k with rfl | hjk
        · simp [Pi.single_apply, hI0]
        · have hne : 2 * (j:ℕ) + 0 ≠ 2 * (k:ℕ) := by
            intro e; apply hjk; ext; omega
          rw [if_neg hne, mul_zero, Pi.single_apply, if_neg (Ne.symm hjk), mul_zero]
      · intro p _ hp
        rw [Finsupp.single_apply, if_neg (fun e => hp e.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin 1005)).span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)
  have hVeq : V = (LinearMap.ker G).map Φ := by
    ext P
    rw [V_def, Submodule.mem_map]
    constructor
    · rintro ⟨hb, hdg⟩
      obtain ⟨c, hc_def⟩ : ∃ c : ↥T →₀ ℝ, ∀ p, c p = coeff (mon p.1) P :=
        ⟨Finsupp.equivFunOnFinite.symm (fun p : ↥T => coeff (mon p.1) P), fun p => by simp⟩
      have hc : Φ c = P := by
        ext m
        by_cases hm : m 0 + m 1 ≤ 2009
        · rw [hdeg' c m hm, hc_def]
          simp [hmon_surj]
        · rw [hdeg c m (by omega)]
          by_contra hne
          have hne' : coeff m P ≠ 0 := fun h => hne h.symm
          have h1 := MvPolynomial.le_totalDegree (mem_support_iff.mpr hne')
          have hs2 : (m.sum fun _ e => e) = m 0 + m 1 := by simp [Finsupp.sum_fintype, Fin.sum_univ_two]
          omega
      refine ⟨c, LinearMap.mem_ker.mpr ((hbal c).mp ?_), hc⟩
      rw [hc]; exact hb
    · rintro ⟨c, hc0, rfl⟩
      refine ⟨(hbal c).mpr (LinearMap.mem_ker.mp hc0), ?_⟩
      unfold MvPolynomial.totalDegree
      apply Finset.sup_le
      intro s hs
      have hs' : coeff s (Φ c) ≠ 0 := mem_support_iff.mp hs
      have hle : s 0 + s 1 ≤ 2009 := by
        by_contra hbig
        exact hs' (hdeg c s (by omega))
      have hs2 : (s.sum fun _ e => e) = s 0 + s 1 := by simp [Finsupp.sum_fintype, Fin.sum_univ_two]
      show s.sum (fun _ e => e) ≤ 2009
      omega
  have hrk := LinearMap.rank_range_add_rank_ker G
  rw [hrange, rank_top, rank_fin_fun, rank_finsupp_self] at hrk
  simp only [Cardinal.lift_id, Cardinal.mk_fintype, Fintype.card_coe, hTc] at hrk
  rw [hVeq, (Submodule.equivMapOfInjective Φ hΦinj (LinearMap.ker G)).symm.rank_eq]
  have hfin : Module.rank ℝ (LinearMap.ker G) < Cardinal.aleph0 := by
    have h1 : Module.rank ℝ (LinearMap.ker G) ≤ ((2021055:ℕ):Cardinal) := by
      rw [← hrk]; exact self_le_add_left _ _
    exact lt_of_le_of_lt h1 (Cardinal.natCast_lt_aleph0)
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at hrk ⊢
  norm_cast at hrk
  have hn' : n = 2020050 := by omega
  simp [putnam_2009_b4_solution, hn']
