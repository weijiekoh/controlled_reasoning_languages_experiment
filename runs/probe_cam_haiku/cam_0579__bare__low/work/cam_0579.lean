import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-579»

open scoped BigOperators
theorem convexOn_iff_convex_and_hessian_posSemidef
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hCconv : Convex ℝ C)
    (hCopen : IsOpen C)
    (_hC2 : ∀ x ∈ C, ContDiffAt ℝ 2 f x) :
    ConvexOn ℝ C f ↔
      ∀ x ∈ C, ∀ z : Fin n → ℝ,
        0 ≤
          ∑ i : Fin n, z i *
            ∑ j : Fin n,
              z j *
                ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) x)
                  (Pi.single i (1 : ℝ))) := by
  have L1 : ∀ (T : Set ℝ), IsOpen T → ∀ (g : ℝ → ℝ), ConvexOn ℝ T g →
      (∀ t ∈ T, DifferentiableAt ℝ g t) → (∀ t ∈ T, DifferentiableAt ℝ (deriv g) t) →
      ∀ t0 ∈ T, 0 ≤ deriv (deriv g) t0 := by
    intro T hT g hg hd hd2 t0 ht0
    have hmono : MonotoneOn (deriv g) T := by
      have := hg.monotoneOn_derivWithin (fun t ht => (hd t ht).differentiableWithinAt)
      intro a ha b hb hab
      have h1 := this ha hb hab
      rwa [derivWithin_of_isOpen hT ha, derivWithin_of_isOpen hT hb] at h1
    by_contra hneg
    push_neg at hneg
    have hH : HasDerivAt (deriv g) (deriv (deriv g) t0) t0 := (hd2 t0 ht0).hasDerivAt
    rw [hasDerivAt_iff_tendsto_slope] at hH
    have hpos : ∀ᶠ t in nhdsWithin t0 (Set.Ioi t0), slope (deriv g) t0 t < 0 := by
      have h2 := (tendsto_order.1 hH).2 0 hneg
      exact h2.filter_mono (nhdsWithin_mono _ (fun t (ht : t0 < t) => (ne_of_gt ht : t ≠ t0)))
    have hT' : ∀ᶠ t in nhdsWithin t0 (Set.Ioi t0), t ∈ T :=
      nhdsWithin_le_nhds (hT.mem_nhds ht0)
    obtain ⟨t, hslope, htT, ht⟩ := (hpos.and (hT'.and self_mem_nhdsWithin)).exists
    have ht' : t0 < t := ht
    rw [slope_def_field] at hslope
    have hlt : deriv g t < deriv g t0 := by
      rcases div_neg_iff.1 hslope with ⟨_, h2⟩ | ⟨h1, _⟩ <;> linarith
    exact absurd (hmono ht0 htT ht'.le) (not_le.2 hlt)
  
  have PL : ∀ (p : Fin n → ℝ), ContDiffAt ℝ 2 f p → ∀ (z : Fin n → ℝ),
      fderiv ℝ (fun y => fderiv ℝ f y z) p z =
        ∑ i : Fin n, z i * ∑ j : Fin n, z j *
          ((fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) p) (Pi.single i (1 : ℝ))) := by
    intro p hp z
    have hF : ContDiffAt ℝ 1 (fderiv ℝ f) p := hp.fderiv_right (by norm_num)
    have hFd : DifferentiableAt ℝ (fderiv ℝ f) p := hF.differentiableAt (by norm_num)
    have hw : ∀ w : Fin n → ℝ, w = ∑ j, w j • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
      intro w; ext i; simp [Finset.sum_apply, Pi.single_apply]
    have hsplit : ∀ w : Fin n → ℝ, (fun y => fderiv ℝ f y w) =
        fun y => ∑ j, w j * fderiv ℝ f y (Pi.single j (1 : ℝ)) := by
      intro w; funext y
      conv_lhs => rw [hw w]
      simp [map_sum]
    have hD : ∀ j : Fin n, HasFDerivAt (fun y => fderiv ℝ f y (Pi.single j (1 : ℝ)))
        (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) p) p := by
      intro j
      exact (hFd.clm_apply (differentiableAt_const _)).hasFDerivAt
    have hH : HasFDerivAt (fun y => ∑ j, z j * fderiv ℝ f y (Pi.single j (1 : ℝ)))
        (∑ j, z j • fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) p) p := by
      have := HasFDerivAt.sum (u := Finset.univ)
        (A := fun j y => z j * fderiv ℝ f y (Pi.single j (1 : ℝ)))
        (A' := fun j => z j • fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) p)
        (fun j _ => (hD j).const_mul (z j))
      simpa [Finset.sum_fn] using this
    have hfd := hH.fderiv
    rw [hsplit z, hfd]
    have hDz : ∀ j : Fin n, (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) p) z =
        ∑ i, z i * (fderiv ℝ (fun y => (fderiv ℝ f y) (Pi.single j (1 : ℝ))) p) (Pi.single i (1 : ℝ)) := by
      intro j
      conv_lhs => rw [hw z]
      simp [map_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp_rw [hDz, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  
  have hline : ∀ (x v : Fin n → ℝ), ∃ A : ℝ →ᵃ[ℝ] (Fin n → ℝ), ∀ t, A t = x + t • v := by
    intro x v
    refine ⟨⟨fun t => x + t • v, LinearMap.smulRight LinearMap.id v, ?_⟩, fun t => rfl⟩
    intro p q
    simp only [vadd_eq_add, LinearMap.smulRight_apply, LinearMap.id_apply, add_smul]
    abel
  have hlineD : ∀ (x v : Fin n → ℝ) (t : ℝ), HasDerivAt (fun s : ℝ => x + s • v) v t := by
    intro x v t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have chain : ∀ (φ : (Fin n → ℝ) → ℝ) (x z : Fin n → ℝ) (t : ℝ),
      DifferentiableAt ℝ φ (x + t • z) →
        HasDerivAt (fun s : ℝ => φ (x + s • z)) (fderiv ℝ φ (x + t • z) z) t := by
    intro φ x z t hφ
    have h := hφ.hasFDerivAt.comp_hasDerivAt t (hlineD x z t)
    exact h
  have hdiffC : ∀ p ∈ C, DifferentiableAt ℝ f p := fun p hp =>
    (_hC2 p hp).differentiableAt (by norm_num)
  constructor
  · intro hconv x hx z
    have hPgen : ∀ p ∈ C, DifferentiableAt ℝ (fun y => fderiv ℝ f y z) p := fun p hp =>
      ((_hC2 p hp).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.clm_apply (differentiableAt_const _)
    obtain ⟨A, hA⟩ := hline x z
    set T : Set ℝ := {t | x + t • z ∈ C} with hTdef
    have hTopen : IsOpen T := hCopen.preimage (by fun_prop)
    have hT0 : (0:ℝ) ∈ T := by simpa [hTdef] using hx
    have hTA : T = ⇑A ⁻¹' C := by
      ext t; simp [hTdef, hA]
    have hTconv : ConvexOn ℝ T (fun t => f (x + t • z)) := by
      have h1 := hconv.comp_affineMap A
      have hfA : (f ∘ ⇑A) = fun t => f (x + t • z) := funext (fun t => by simp [hA])
      rw [hfA, ← hTA] at h1
      exact h1
    have hderg : ∀ t ∈ T, HasDerivAt (fun s : ℝ => f (x + s • z)) (fderiv ℝ f (x + t • z) z) t :=
      fun t ht => chain f x z t (hdiffC _ ht)
    have hdiffg : ∀ t ∈ T, DifferentiableAt ℝ (fun s : ℝ => f (x + s • z)) t :=
      fun t ht => (hderg t ht).differentiableAt
    have hev : ∀ t ∈ T, deriv (fun s : ℝ => f (x + s • z)) =ᶠ[𝓝 t] fun s => fderiv ℝ f (x + s • z) z := by
      intro t ht
      exact Filter.eventually_of_mem (hTopen.mem_nhds ht) (fun s hs => (hderg s hs).deriv)
    have hdiffD : ∀ t ∈ T, DifferentiableAt ℝ (deriv (fun s : ℝ => f (x + s • z))) t := by
      intro t ht
      have hline2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • z) z)
          (fderiv ℝ (fun y => fderiv ℝ f y z) (x + t • z) z) t :=
        chain (fun y => fderiv ℝ f y z) x z t (hPgen _ ht)
      exact hline2.differentiableAt.congr_of_eventuallyEq (hev t ht)
    have hL := L1 T hTopen _ hTconv hdiffg hdiffD 0 hT0
    have h0 : deriv (deriv (fun s : ℝ => f (x + s • z))) 0 = fderiv ℝ (fun y => fderiv ℝ f y z) x z := by
      rw [(hev 0 hT0).deriv_eq]
      have hline2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • z) z)
          (fderiv ℝ (fun y => fderiv ℝ f y z) (x + (0:ℝ) • z) z) 0 :=
        chain (fun y => fderiv ℝ f y z) x z 0 (hPgen _ hT0)
      rw [hline2.deriv]
      simp
    rw [h0, PL x (_hC2 x hx) z] at hL
    exact hL
  · intro hPSD
    refine ⟨hCconv, ?_⟩
    intro x hx y hy a b ha hb hab
    set v := y - x with hv
    have hPgen : ∀ p ∈ C, ∀ w : Fin n → ℝ, DifferentiableAt ℝ (fun y => fderiv ℝ f y w) p := fun p hp w =>
      ((_hC2 p hp).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.clm_apply (differentiableAt_const _)
    obtain ⟨A, hA⟩ := hline x v
    set D : Set ℝ := {t | x + t • v ∈ C} with hDdef
    have hDopen : IsOpen D := hCopen.preimage (by fun_prop)
    have hDconv : Convex ℝ D := by
      have h1 := hCconv.affine_preimage A
      have hset : D = ⇑A ⁻¹' C := by ext t; simp [hDdef, hA]
      rw [hset]; exact h1
    have h0D : (0:ℝ) ∈ D := by simpa [hDdef] using hx
    have h1D : (1:ℝ) ∈ D := by simpa [hDdef, hv] using hy
    have hderg : ∀ t ∈ D, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + t • v) v) t :=
      fun t ht => chain f x v t (hdiffC _ ht)
    have hdiffg : ∀ t ∈ D, DifferentiableAt ℝ (fun s : ℝ => f (x + s • v)) t :=
      fun t ht => (hderg t ht).differentiableAt
    have hev : ∀ t ∈ D, deriv (fun s : ℝ => f (x + s • v)) =ᶠ[𝓝 t] fun s => fderiv ℝ f (x + s • v) v := by
      intro t ht
      exact Filter.eventually_of_mem (hDopen.mem_nhds ht) (fun s hs => (hderg s hs).deriv)
    have hsec : ∀ t ∈ D, 0 ≤ deriv (deriv (fun s : ℝ => f (x + s • v))) t := by
      intro t ht
      have hline2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
          (fderiv ℝ (fun y => fderiv ℝ f y v) (x + t • v) v) t :=
        chain (fun y => fderiv ℝ f y v) x v t (hPgen _ ht v)
      rw [(hev t ht).deriv_eq, hline2.deriv, PL _ (_hC2 _ ht) v]
      exact hPSD _ ht v
    have hdiffD : ∀ t ∈ D, DifferentiableAt ℝ (deriv (fun s : ℝ => f (x + s • v))) t := by
      intro t ht
      have hline2 : HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
          (fderiv ℝ (fun y => fderiv ℝ f y v) (x + t • v) v) t :=
        chain (fun y => fderiv ℝ f y v) x v t (hPgen _ ht v)
      exact hline2.differentiableAt.congr_of_eventuallyEq (hev t ht)
    have hcv : ConvexOn ℝ D (fun s : ℝ => f (x + s • v)) := by
      apply convexOn_of_deriv2_nonneg hDconv
      · intro t ht
        exact (hdiffg t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [hDopen.interior_eq] at ht
        exact (hdiffg t ht).differentiableWithinAt
      · intro t ht
        rw [hDopen.interior_eq] at ht
        exact (hdiffD t ht).differentiableWithinAt
      · intro t ht
        rw [hDopen.interior_eq] at ht
        exact hsec t ht
    have key := hcv.2 h0D h1D ha hb hab
    have hxy : a • x + b • y = x + b • v := by
      have : a = 1 - b := by linarith
      subst this
      simp only [hv, sub_smul, one_smul, smul_sub]
      abel
    have hxv : x + v = y := by rw [hv]; abel
    have key2 : f (x + b • v) ≤ a * f x + b * f y := by
      have h := key
      simp only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero, zero_smul, one_smul] at h
      rw [hxv] at h
      exact h
    rw [hxy]
    simp only [smul_eq_mul]
    exact key2


end «CAM-Bench-579»
