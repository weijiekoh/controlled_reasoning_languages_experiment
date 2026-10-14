import Mathlib

open Metric Filter Topology Set Nat

noncomputable abbrev putnam_2008_b3_solution : ℝ := Real.sqrt 2 / 2
/--
What is the largest possible radius of a circle contained in a $4$-dimensional hypercube of side length $1$?
-/
theorem putnam_2008_b3
    (H : Set (EuclideanSpace ℝ (Fin 4)))
    (H_def : H = {P : EuclideanSpace ℝ (Fin 4) | ∀ i : Fin 4, |P i| ≤ 1 / 2})
    (contains : ℝ → Prop)
    (contains_def : ∀ r, contains r ↔
      ∃ᵉ (A : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 4))) (C ∈ A),
        Module.finrank ℝ A.direction = 2 ∧
        sphere C r ∩ A ⊆ H) :
    IsGreatest contains putnam_2008_b3_solution := by
  subst H_def
  constructor
  · show contains _
    rw [contains_def]
    let e0 : EuclideanSpace ℝ (Fin 4) := !₂[1/2, 1/2, 0, 0]
    let e1 : EuclideanSpace ℝ (Fin 4) := !₂[0, 0, 1/2, 1/2]
    refine ⟨AffineSubspace.mk' 0 (Submodule.span ℝ {e0, e1}), 0, ?_, ?_, ?_⟩
    · simp
    · rw [AffineSubspace.direction_mk']
      have hli : LinearIndependent ℝ ![e0, e1] := by
        rw [LinearIndependent.pair_iff]
        intro s t h
        have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 0) h
        have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin 4) => x 2) h
        simp [e0, e1] at h0 h2
        constructor <;> linarith
      have := finrank_span_eq_card hli
      have hr : Set.range ![e0, e1] = {e0, e1} := by
        ext x; simp [Fin.exists_fin_two]; tauto
      rw [hr] at this
      simpa using this
    · rintro P ⟨hP1, hP2⟩
      rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, sub_zero, Submodule.mem_span_pair] at hP2
      obtain ⟨a, b, rfl⟩ := hP2
      rw [mem_sphere_zero_iff_norm] at hP1
      have h2 := congrArg (fun x => x^2) hP1
      simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, putnam_2008_b3_solution] at h2
      rw [div_pow, Real.sq_sqrt (by norm_num)] at h2
      simp [e0, e1] at h2
      have hab : a^2+b^2=1 := by
        simp only [mul_pow, sq_abs] at h2; nlinarith
      intro i
      fin_cases i <;> simp [e0, e1] <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a-b)]
  · intro r hr
    change contains r at hr
    rw [contains_def] at hr
    obtain ⟨A, C, hC, hdim, hsub⟩ := hr
    rcases le_or_gt r 0 with hr0 | hr0
    · have : (0:ℝ) ≤ putnam_2008_b3_solution := by unfold putnam_2008_b3_solution; positivity
      linarith
    let b := (stdOrthonormalBasis ℝ A.direction).reindex (finCongr hdim)
    have hon := b.orthonormal
    set u : EuclideanSpace ℝ (Fin 4) := ((b 0 : A.direction) : EuclideanSpace ℝ (Fin 4)) with hu
    set v : EuclideanSpace ℝ (Fin 4) := ((b 1 : A.direction) : EuclideanSpace ℝ (Fin 4)) with hv
    have hu1 : ‖u‖ = 1 := hon.1 0
    have hv1 : ‖v‖ = 1 := hon.1 1
    have huv : inner ℝ u v = 0 := by
      have := hon.2 (show (0 : Fin 2) ≠ 1 by decide)
      exact this
    have key : ∀ a c : ℝ, a^2 + c^2 = 1 → ∀ i, |C i + r * (a * u i + c * v i)| ≤ 1/2 := by
      intro a c hac i
      have hmem : a • u + c • v ∈ A.direction :=
        A.direction.add_mem (A.direction.smul_mem _ (b 0).2) (A.direction.smul_mem _ (b 1).2)
      have hn : ‖a • u + c • v‖ = 1 := by
        have : ‖a • u + c • v‖^2 = 1 := by
          rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, huv, hu1, hv1]
          simp [mul_pow, sq_abs]; linarith
        nlinarith [norm_nonneg (a • u + c • v)]
      have hP := hsub (show C + r • (a • u + c • v) ∈ sphere C r ∩ (A : Set _) from ⟨?_, ?_⟩) i
      · simpa [mul_add] using hP
      · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, hn, Real.norm_eq_abs, abs_of_pos hr0, mul_one]
      · rw [add_comm]; exact AffineSubspace.vadd_mem_of_mem_direction (A.direction.smul_mem r hmem) hC
    have hi : ∀ i, r^2 * (u i ^2 + v i ^2) ≤ 1/4 := by
      intro i
      by_cases hs : u i ^2 + v i ^2 = 0
      · rw [hs]; norm_num
      have hpos : 0 < u i ^2 + v i ^2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
      set s := Real.sqrt (u i ^2 + v i ^2) with hsdef
      have hs2 : s^2 = u i ^2 + v i ^2 := Real.sq_sqrt hpos.le
      have hs0 : 0 < s := Real.sqrt_pos.2 hpos
      have h1 := key (u i / s) (v i / s) (by field_simp; linarith) i
      have h2 := key (-(u i / s)) (-(v i / s)) (by field_simp; linarith) i
      have e1 : u i / s * u i + v i / s * v i = s := by field_simp; linarith
      have e2 : -(u i / s) * u i + -(v i / s) * v i = -s := by field_simp; linarith
      rw [e1] at h1
      rw [e2] at h2
      rw [abs_le] at h1 h2
      have : r * s ≤ 1/2 := by linarith [h1.2, h2.1]
      rw [← hs2]
      nlinarith [mul_pos hr0 hs0]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    have hu2 : ∑ i, u i ^2 = 1 := by
      have := EuclideanSpace.norm_sq_eq u
      simp only [Real.norm_eq_abs, sq_abs] at this
      rw [hu1] at this; linarith
    have hv2 : ∑ i, v i ^2 = 1 := by
      have := EuclideanSpace.norm_sq_eq v
      simp only [Real.norm_eq_abs, sq_abs] at this
      rw [hv1] at this; linarith
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, hu2, hv2] at hsum
    simp at hsum
    have hr2 : r^2 ≤ 1/2 := by linarith
    unfold putnam_2008_b3_solution
    have : r ≤ Real.sqrt (1/2) := Real.le_sqrt_of_sq_le hr2
    have h3 : Real.sqrt (1/2) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by positivity)]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    linarith
