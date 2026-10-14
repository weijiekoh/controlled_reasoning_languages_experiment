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
  -- analytic facts
  have hodd_int : ∀ a b : ℕ, Odd (a+b) → ∫ t in (0:ℝ)..2*π, cos t ^ a * sin t ^ b = 0 := by
    intro a b hab
    set f : ℝ → ℝ := fun t => cos t ^ a * sin t ^ b with hf
    have hodd : ∀ t, f (t + π) = -f t := by
      intro t
      simp only [hf, cos_add_pi, sin_add_pi]
      have : (-cos t)^a * (-sin t)^b = (-1)^a * (-1)^b * (cos t ^ a * sin t ^ b) := by ring
      rw [this, ← pow_add, Odd.neg_one_pow hab]
      ring
    have hper : Function.Periodic f (2*π) := by
      intro t; simp only [hf, cos_add_two_pi, sin_add_two_pi]
    have h1 := hper.intervalIntegral_add_eq 0 π
    simp only [zero_add] at h1
    have h2 : ∫ x in (0:ℝ)..2*π, f (x + π) = ∫ x in π..2*π+π, f x := by
      rw [intervalIntegral.integral_comp_add_right]; simp
    simp only [hodd, intervalIntegral.integral_neg] at h2
    rw [show 2*π+π = π + 2*π by ring] at h2
    have : ∫ t in (0:ℝ)..2*π, f t = ∫ t in (0:ℝ)..2*π, cos t ^ a * sin t ^ b := rfl
    rw [← this]
    linarith
  have hev : ∀ d : ℕ, Even d → ∫ t in (0:ℝ)..2*π, cos t ^ d ≠ 0 := by
    intro d hd
    have hp : Function.Periodic (fun t => sin t ^ d) (2*π) := by
      intro t; simp only [sin_add_two_pi]
    have h1 := hp.intervalIntegral_add_eq 0 (π/2)
    simp only [zero_add] at h1
    have e : ∫ t in (0:ℝ)..2*π, cos t ^ d = ∫ t in (0:ℝ)..2*π, sin (t + π/2) ^ d := by
      congr 1; funext t; simp only [sin_add_pi_div_two]
    have h2 : ∫ t in (0:ℝ)..2*π, sin (t + π/2) ^ d = ∫ t in (0:ℝ)..2*π, sin t ^ d := by
      rw [intervalIntegral.integral_comp_add_right (fun t => sin t ^ d)]
      rw [zero_add, show 2*π+π/2 = π/2+2*π by ring]
      exact h1.symm
    have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => sin t ^ d) MeasureTheory.volume a b :=
      fun a b => Continuous.intervalIntegrable (by fun_prop) _ _
    have h3 : (∫ t in (0:ℝ)..2*π, sin t ^ d) = (∫ t in (0:ℝ)..π, sin t ^ d) + (∫ t in π..2*π, sin t ^ d) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hi 0 π) (hi π (2*π))]
    have h4 : ∫ t in π..2*π, sin t ^ d = ∫ t in (0:ℝ)..π, sin t ^ d := by
      have := intervalIntegral.integral_comp_add_right (fun t => sin t ^ d) (a := 0) (b := π) π
      simp only [zero_add] at this
      rw [show 2*π = π + π by ring, ← this]
      congr 1; funext t
      simp only [sin_add_pi]
      rw [Even.neg_pow hd]
    have hpos : 0 < ∫ t in (0:ℝ)..π, sin t ^ d := integral_sin_pow_pos d
    rw [e, h2, h3, h4]
    exact (add_pos hpos hpos).ne'
  obtain ⟨J, hJ⟩ : ∃ J : (Fin 2 →₀ ℕ) → ℝ, ∀ n, J n = ∫ t in (0:ℝ)..2*π, cos t ^ n 0 * sin t ^ n 1 :=
    ⟨_, fun n => rfl⟩
  have hJodd : ∀ n : Fin 2 →₀ ℕ, Odd (n 0 + n 1) → J n = 0 := fun n hn => by
    rw [hJ]; exact hodd_int _ _ hn
  have hJne : ∀ d : ℕ, Even d → J (Finsupp.single 0 d) ≠ 0 := by
    intro d hd
    rw [hJ]; simpa using hev d hd
  have hint : ∀ P : MvPolynomial (Fin 2) ℝ, ∀ r : ℝ,
      (∫ t in (0:ℝ)..2*π, eval ![r * cos t, r * sin t] P)
        = ∑ n ∈ P.support, coeff n P * (r ^ (n 0 + n 1) * J n) := by
    intro P r
    have hfun : (fun t => eval ![r * cos t, r * sin t] P)
        = fun t => ∑ n ∈ P.support, coeff n P * (r ^ (n 0 + n 1) * (cos t ^ n 0 * sin t ^ n 1)) := by
      funext t
      rw [eval_eq']
      apply Finset.sum_congr rfl
      intro n _
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    rw [hfun, intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro n _
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hJ]
    · intro n _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  -- the monomial index sets
  have hsum : ∀ n : Fin 2 →₀ ℕ, (n.sum fun _ e => e) = n 0 + n 1 := fun n => by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  obtain ⟨T, hT, hTcard⟩ : ∃ T : ℕ → Finset (Fin 2 →₀ ℕ),
      (∀ d n, n ∈ T d ↔ n 0 + n 1 = d) ∧ (∀ d, (T d).card = d + 1) := by
    have inj : Function.Injective (fun p : ℕ × ℕ => (Finsupp.single 0 p.1 + Finsupp.single 1 p.2 : Fin 2 →₀ ℕ)) := by
      intro p q h
      have h0 := congrArg (fun n : Fin 2 →₀ ℕ => n 0) h
      have h1 := congrArg (fun n : Fin 2 →₀ ℕ => n 1) h
      simp at h0 h1
      exact Prod.ext h0 h1
    refine ⟨fun d => (Finset.HasAntidiagonal.antidiagonal d).image
      (fun p : ℕ × ℕ => (Finsupp.single 0 p.1 + Finsupp.single 1 p.2 : Fin 2 →₀ ℕ)), ?_, ?_⟩
    · intro d n
      simp only [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal]
      constructor
      · rintro ⟨p, hp, rfl⟩
        simp [hp]
      · intro h
        refine ⟨(n 0, n 1), by simpa using h, ?_⟩
        ext i
        fin_cases i <;> simp
    · intro d
      rw [Finset.card_image_of_injective _ inj, Finset.Nat.card_antidiagonal]
  obtain ⟨c, hc⟩ : ∃ c : ℕ → (MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ),
      ∀ d P, c d P = ∑ n ∈ T d, coeff n P * J n := by
    refine ⟨fun d => { toFun := fun P => ∑ n ∈ T d, coeff n P * J n
                       map_add' := ?_
                       map_smul' := ?_ }, fun d P => rfl⟩
    · intro P Q
      simp [coeff_add, add_mul, Finset.sum_add_distrib]
    · intro a P
      simp [coeff_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hdisj : ∀ (s : Finset ℕ), (↑s : Set ℕ).PairwiseDisjoint T := by
    intro s d _ e _ hde
    exact Finset.disjoint_left.mpr fun n h1 h2 => hde (((hT d n).mp h1).symm.trans ((hT e n).mp h2))
  have hF2 : ∀ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ 2009 → ∀ r : ℝ,
      (∫ t in (0:ℝ)..2*π, eval ![r * cos t, r * sin t] P) = ∑ d ∈ Finset.range 2010, r ^ d * c d P := by
    intro P hP r
    rw [hint]
    have hsupp : ∀ n ∈ P.support, n 0 + n 1 < 2010 := by
      intro n hn
      have h1 := le_totalDegree hn
      rw [hsum] at h1
      omega
    have hsub : P.support ⊆ (Finset.range 2010).biUnion T := by
      intro n hn
      rw [Finset.mem_biUnion]
      exact ⟨n 0 + n 1, Finset.mem_range.mpr (hsupp n hn), (hT _ n).mpr rfl⟩
    have hz : ∀ n ∈ (Finset.range 2010).biUnion T, n ∉ P.support →
        coeff n P * (r ^ (n 0 + n 1) * J n) = 0 := by
      intro n _ hn
      rw [MvPolynomial.notMem_support_iff.mp hn]
      simp
    rw [Finset.sum_subset hsub hz, Finset.sum_biUnion (hdisj _)]
    apply Finset.sum_congr rfl
    intro d _
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [(hT d n).mp hn]
    ring
  have hcodd : ∀ d, Odd d → ∀ P, c d P = 0 := by
    intro d hd P
    rw [hc]
    apply Finset.sum_eq_zero
    intro n hn
    have : Odd (n 0 + n 1) := by rw [(hT d n).mp hn]; exact hd
    rw [hJodd n this, mul_zero]
  have hpoly : ∀ p : Polynomial ℝ, (∀ r : ℝ, 0 < r → p.eval r = 0) → p = 0 := fun p hp0 =>
    Polynomial.eq_zero_of_infinite_isRoot p (Set.Infinite.mono (fun r hr => hp0 r hr) (Set.Ioi_infinite 0))
  have hbal : ∀ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ 2009 →
      (IsBalanced P ↔ ∀ d ∈ Finset.range 2010, c d P = 0) := by
    intro P hP
    rw [IsBalanced_def]
    have hrr : ∀ r : ℝ, r > 0 → ((∫ t in (0:ℝ)..(2 * π), eval ![r * cos t, r * sin t] P) / (2 * π * r) = 0
        ↔ ∑ d ∈ Finset.range 2010, r ^ d * c d P = 0) := by
      intro r hr0
      rw [hF2 P hP r, div_eq_zero_iff]
      have : (0:ℝ) < 2 * π * r := by positivity
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h this.ne'
      · intro h; exact Or.inl h
    constructor
    · intro h
      have hzero := hpoly (∑ d ∈ Finset.range 2010, Polynomial.C (c d P) * Polynomial.X ^ d) (by
        intro r hr0
        simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        refine Eq.trans ?_ ((hrr r hr0).mp (h r hr0))
        apply Finset.sum_congr rfl
        intro d _
        ring)
      intro d hd
      have hcoeff := congrArg (fun q => Polynomial.coeff q d) hzero
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hcoeff
      simpa [Finset.sum_ite_eq, hd] using hcoeff
    · intro h r hr0
      rw [hrr r hr0]
      apply Finset.sum_eq_zero
      intro d hd
      rw [h d hd, mul_zero]
  -- the balanced condition as a finite system of even-degree constraints
  have hF5 : ∀ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ 2009 →
      (IsBalanced P ↔ ∀ k : Fin 1005, c (2 * (k : ℕ)) P = 0) := by
    intro P hP
    rw [hbal P hP]
    constructor
    · intro h k
      apply h
      exact Finset.mem_range.mpr (by have := k.isLt; omega)
    · intro h d hd
      have hd' := Finset.mem_range.mp hd
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | ho
      · have := h ⟨k, by omega⟩
        simp only at this
        rwa [show 2 * k = d by omega] at this
      · exact hcodd d ho P
  -- the finite-dimensional space W
  have hsetU : {n : Fin 2 →₀ ℕ | (n.sum fun _ e => e) ≤ 2009} = ↑((Finset.range 2010).biUnion T) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Set.mem_Iio,
      Finset.mem_coe, hsum, hT]
    constructor
    · intro h
      exact ⟨n 0 + n 1, by omega, rfl⟩
    · rintro ⟨d, hd, hdn⟩
      omega
  have hcardU : Nat.card ↥{n : Fin 2 →₀ ℕ | (n.sum fun _ e => e) ≤ 2009} = 2021055 := by
    rw [hsetU, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_biUnion (hdisj _)]
    simp only [hTcard]
    have hg := Finset.sum_range_id_mul_two 2010
    have hs : ∑ d ∈ Finset.range 2010, (d + 1) = (∑ d ∈ Finset.range 2010, d) + 2010 := by
      rw [Finset.sum_add_distrib]; simp
    omega
  let W := restrictTotalDegree (Fin 2) ℝ 2009
  have hb : Module.Basis ↥{n : Fin 2 →₀ ℕ | (n.sum fun _ e => e) ≤ 2009} ℝ W :=
    basisRestrictSupport ℝ _
  have hfin : Finite ↥{n : Fin 2 →₀ ℕ | (n.sum fun _ e => e) ≤ 2009} :=
    Nat.finite_of_card_ne_zero (by rw [hcardU]; norm_num)
  have hfinW' : Module.Finite ℝ W := Module.Finite.of_basis hb
  have hfinW : Module.finrank ℝ W = 2021055 := by
    rw [Module.finrank_eq_nat_card_basis hb, hcardU]
  have hmemW : ∀ P : MvPolynomial (Fin 2) ℝ, P ∈ W ↔ P.totalDegree ≤ 2009 :=
    fun P => mem_restrictTotalDegree (Fin 2) 2009 P
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W →ₗ[ℝ] (Fin 1005 → ℝ),
      ∀ x k, Ψ x k = c (2 * (k : ℕ)) (x : MvPolynomial (Fin 2) ℝ) :=
    ⟨LinearMap.pi (fun k : Fin 1005 => (c (2 * (k : ℕ))).comp W.subtype), fun x k => rfl⟩
  have hsing : ∀ k : Fin 1005, Pi.single k (1:ℝ) ∈ LinearMap.range Ψ := by
    intro k
    have hmem : (X 0 ^ (2 * (k:ℕ)) : MvPolynomial (Fin 2) ℝ) ∈ W := by
      rw [hmemW, totalDegree_X_pow]
      have := k.isLt
      omega
    have hcX : ∀ m d : ℕ, c d (X 0 ^ m) = if m = d then J (Finsupp.single 0 m) else 0 := by
      intro m d
      rw [hc, X_pow_eq_monomial]
      simp [coeff_monomial, hT, eq_comm]
    have hne := hJne (2 * (k:ℕ)) ⟨k, by ring⟩
    refine ⟨(1 / J (Finsupp.single 0 (2 * (k:ℕ)))) • ⟨X 0 ^ (2 * (k:ℕ)), hmem⟩, ?_⟩
    funext j
    rw [hΨ, Submodule.coe_smul, map_smul, smul_eq_mul, hcX, Pi.single_apply]
    by_cases hjk : j = k
    · have h2 : 2 * (k:ℕ) = 2 * (j:ℕ) := by rw [hjk]
      rw [if_pos h2, if_pos hjk, one_div, inv_mul_cancel₀ hne]
    · have h2 : ¬ (2 * (k:ℕ) = 2 * (j:ℕ)) := fun h => hjk (Fin.ext (by omega))
      rw [if_neg h2, if_neg hjk, mul_zero]
  have hrange : LinearMap.range Ψ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k : Fin 1005, v k • Pi.single k (1:ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hsing k))
  have hrank := LinearMap.finrank_range_add_finrank_ker Ψ
  rw [hrange, finrank_top, Module.finrank_fin_fun, hfinW] at hrank
  have hKfin : Module.finrank ℝ (LinearMap.ker Ψ) = 2020050 := by omega
  have hV : V = (LinearMap.ker Ψ).map W.subtype := by
    ext P
    constructor
    · intro hP
      obtain ⟨hb', hdeg⟩ := (V_def P).mp hP
      refine ⟨⟨P, (hmemW P).mpr hdeg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      funext k
      rw [hΨ, (hF5 P hdeg).mp hb' k]
      rfl
    · rintro ⟨x, hx, rfl⟩
      have hdeg : (x : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2009 := (hmemW _).mp x.2
      refine (V_def _).mpr ⟨(hF5 _ hdeg).mpr ?_, hdeg⟩
      intro k
      have := congrFun (LinearMap.mem_ker.mp hx) k
      rw [hΨ] at this
      simpa using this
  rw [hV, ← (Submodule.equivMapOfInjective W.subtype (Submodule.injective_subtype W)
    (LinearMap.ker Ψ)).rank_eq, ← Module.finrank_eq_rank, hKfin]
