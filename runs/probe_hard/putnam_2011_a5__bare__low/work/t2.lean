import Mathlib
open Topology Filter
example (g : ℝ → ℝ) (F : (Fin 2 → ℝ) → ℝ) (hgc : Continuous g) (hgp : ∀ x, 0 < g x)
  (hpair : ∀ (a b : ℝ → ℝ) (u a' b' : ℝ), HasDerivAt a a' u → HasDerivAt b b' u →
      HasDerivAt (fun w => F ![a w, b w])
        (deriv (fun x => F ![x, b u]) (a u) * a' + deriv (fun y => F ![a u, y]) (b u) * b') u)
  (hcross : ∀ p q, deriv (fun x => F ![x, q]) p * g q + deriv (fun y => F ![p, y]) q * g p = 0) : False := by
  set G : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, g t with hGdef
  have hGs : ∀ x, HasStrictDerivAt G (g x) x := fun x => hgc.integral_hasStrictDerivAt 0 x
  have hG : ∀ x, HasDerivAt G (g x) x := fun x => (hGs x).hasDerivAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hGm : StrictMono G := strictMono_of_deriv_pos (fun x => by rw [(hG x).deriv]; exact hgp x)
  have hopen : IsOpen (Set.range G) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨v, rfl⟩
    have := (hGs v).map_nhds_eq (hgp v).ne'
    rw [← this]; exact Filter.range_mem_map
  have hord : (Set.range G).OrdConnected := (isPreconnected_range hGc).ordConnected
  set ginv : ℝ → ℝ := Function.invFun G with hginvdef
  have hginv : ∀ y ∈ Set.range G, G (ginv y) = y := fun y hy => Function.invFun_eq hy
  have hginv2 : ∀ v, ginv (G v) = v := fun v => Function.leftInverse_invFun hGm.injective v
  have hginvd : ∀ y ∈ Set.range G, HasDerivAt ginv (g (ginv y))⁻¹ y := by
    intro y hy
    have hmono : MonotoneOn ginv (Set.range G) := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
      rw [hginv2, hginv2]; exact hGm.le_iff_le.1 hab
    have hcont : ContinuousAt ginv y := by
      apply continuousAt_of_monotoneOn_of_image_mem_nhds hmono (hopen.mem_nhds hy)
      have : ginv '' Set.range G = Set.univ := by
        ext v; simp only [Set.mem_image, Set.mem_range, Set.mem_univ, iff_true]
        exact ⟨G v, ⟨v, rfl⟩, hginv2 v⟩
      rw [this]; exact Filter.univ_mem
    refine HasDerivAt.of_local_left_inverse hcont (hG _) (hgp _).ne' ?_
    filter_upwards [hopen.mem_nhds hy] with z hz using hginv z hz
  have hinv : ∀ u v u' v', G u - G v = G u' - G v' → F ![u, v] = F ![u', v'] := by
    intro u v u' v' huv
    set d := G u - G v with hd
    let U : Set ℝ := {w | G w - d ∈ Set.range G}
    have hUo : IsOpen U := hopen.preimage (hGc.sub continuous_const)
    have hUc : IsPreconnected U := by
      apply Set.OrdConnected.isPreconnected
      constructor
      intro a ha b hb w hw
      show G w - d ∈ Set.range G
      apply hord.out ha hb
      exact ⟨sub_le_sub_right (hGm.monotone hw.1) _, sub_le_sub_right (hGm.monotone hw.2) _⟩
    set h : ℝ → ℝ := fun w => F ![w, ginv (G w - d)] with hh
    have hder : ∀ w ∈ U, HasDerivAt h 0 w := by
      intro w hw
      have h1 := ((hginvd _ hw).comp w ((hG w).sub_const d))
      have h2 := hpair (fun w => w) (fun w => ginv (G w - d)) w 1 _ (hasDerivAt_id' w) h1
      have h3 := hcross w (ginv (G w - d))
      have hp := hgp (ginv (G w - d))
      convert h2 using 1
      field_simp
      linarith
    have hu : u ∈ U := ⟨v, by simp [hd]⟩
    have hu' : u' ∈ U := ⟨v', by simp [huv]⟩
    have := hUo.is_const_of_deriv_eq_zero hUc (fun w hw => (hder w hw).differentiableAt.differentiableWithinAt) (fun w hw => by simp [(hder w hw).deriv]) hu hu'
    simp only [hh] at this
    have e1 : ginv (G u - d) = v := by rw [hd]; simp [hginv2]
    have e2 : ginv (G u' - d) = v' := by rw [huv]; simp [hginv2]
    rw [e1, e2] at this; exact this
  sorry
