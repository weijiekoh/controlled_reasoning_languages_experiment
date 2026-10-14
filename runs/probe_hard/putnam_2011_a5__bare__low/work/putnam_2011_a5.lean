import Mathlib

open Topology Filter Matrix

/--
Let $F:\mathbb{R}^2 \to \mathbb{R}$ and $g:\mathbb{R} \to \mathbb{R}$ be twice continuously differentiable functions with the following properties:
\begin{itemize}
\item $F(u,u)=0$ for every $u \in \mathbb{R}$;
\item for every $x \in \mathbb{R}$, $g(x)>0$ and $x^2g(x) \leq 1$;
\item for every $(u,v) \in \mathbb{R}^2$, the vector $\nabla F(u,v)$ is either $\mathbf{0}$ or parallel to the vector $\langle g(u),-g(v) \rangle$.
\end{itemize}
Prove that there exists a constant $C$ such that for every $n \geq 2$ and any $x_1,\dots,x_{n+1} \in \mathbb{R}$, we have $\min_{i \neq j} |F(x_i,x_j)| \leq \frac{C}{n}$.
-/
theorem putnam_2011_a5
(F : (Fin 2 → ℝ) → ℝ)
(g : ℝ → ℝ)
(vec : ℝ → ℝ → (Fin 2 → ℝ))
(Fgrad : (Fin 2 → ℝ) → (Fin 2 → ℝ))
(parallel : (Fin 2 → ℝ) → (Fin 2 → ℝ) → Prop)
(hparallel : parallel = (fun u v : Fin 2 → ℝ => ∃ c : ℝ, u = c • v))
(Fgdiff : ContDiff ℝ 2 F ∧ ContDiff ℝ 2 g)
(prop1 : ∀ uu : Fin 2 → ℝ, uu 0 = uu 1 → F uu = 0)
(prop2 : ∀ x : ℝ, g x > 0 ∧ x ^ 2 * g x ≤ 1)
(hvec : ∀ x y : ℝ, (vec x y) 0 = x ∧ (vec x y) 1 = y)
(hFgrad : ∀ uv : Fin 2 → ℝ, Fgrad uv 0 = deriv (fun x : ℝ => F (vec x (uv 1))) (uv 0) ∧ Fgrad uv 1 = deriv (fun y : ℝ => F (vec (uv 0) y)) (uv 1))
(prop3 : ∀ uv : Fin 2 → ℝ, Fgrad uv = 0 ∨ parallel (Fgrad uv) (vec (g (uv 0)) (-g (uv 1))))
: ∃ C : ℝ, ∀ n ≥ 2, ∀ x : Fin (n + 1) → ℝ, sInf {Fxx : ℝ | ∃ i j : Fin (n + 1), i ≠ j ∧ Fxx = |F (vec (x i) (x j))|} ≤ C / n :=
by
  have hv : ∀ x y, vec x y = ![x, y] := by
    intro x y; funext i; fin_cases i
    · simpa using (hvec x y).1
    · simpa using (hvec x y).2
  have hF1 : ContDiff ℝ 2 F := Fgdiff.1
  have hgc : Continuous g := Fgdiff.2.continuous
  have hcurve : ∀ (c : ℝ → Fin 2 → ℝ) (c' : Fin 2 → ℝ) (u : ℝ), HasDerivAt c c' u →
      HasDerivAt (fun w => F (c w)) (fderiv ℝ F (c u) c') u := by
    intro c c' u hc
    have hdF : HasFDerivAt F (fderiv ℝ F (c u)) (c u) :=
      ((hF1.differentiable (by norm_num)) (c u)).hasFDerivAt
    exact hdF.comp_hasDerivAt u hc
  have hpair : ∀ (a b : ℝ → ℝ) (u a' b' : ℝ), HasDerivAt a a' u → HasDerivAt b b' u →
      HasDerivAt (fun w => F ![a w, b w])
        (deriv (fun x => F ![x, b u]) (a u) * a' + deriv (fun y => F ![a u, y]) (b u) * b') u := by
    intro a b u a' b' ha hb
    have hc : HasDerivAt (fun w => ![a w, b w]) ![a', b'] u := by
      rw [hasDerivAt_pi]; intro i; fin_cases i
      · simpa using ha
      · simpa using hb
    have h1 := hcurve _ _ u hc
    have h2 : HasDerivAt (fun x => F ![x, b u]) (fderiv ℝ F ![a u, b u] ![1, 0]) (a u) := by
      have : HasDerivAt (fun x : ℝ => (![x, b u] : Fin 2 → ℝ)) ![1, 0] (a u) := by
        rw [hasDerivAt_pi]; intro i; fin_cases i
        · simpa using hasDerivAt_id' (a u)
        · simpa using hasDerivAt_const (a u) (b u)
      exact hcurve _ _ _ this
    have h3 : HasDerivAt (fun y => F ![a u, y]) (fderiv ℝ F ![a u, b u] ![0, 1]) (b u) := by
      have : HasDerivAt (fun y : ℝ => (![a u, y] : Fin 2 → ℝ)) ![0, 1] (b u) := by
        rw [hasDerivAt_pi]; intro i; fin_cases i
        · simpa using hasDerivAt_const (b u) (a u)
        · simpa using hasDerivAt_id' (b u)
      exact hcurve _ _ _ this
    rw [h2.deriv, h3.deriv]
    have : (![a', b'] : Fin 2 → ℝ) = a' • ![1, 0] + b' • ![0, 1] := by
      funext i; fin_cases i <;> simp
    rw [this, map_add, map_smul, map_smul] at h1
    simpa [mul_comm] using h1
  have hcross : ∀ p q, deriv (fun x => F ![x, q]) p * g q + deriv (fun y => F ![p, y]) q * g p = 0 := by
    intro p q
    have h := hFgrad ![p, q]
    simp only [hv] at h prop3
    have h3 := prop3 ![p, q]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h h3
    rcases h3 with h3 | h3
    · have a0 := congrFun h3 0
      have a1 := congrFun h3 1
      rw [h.1] at a0; rw [h.2] at a1
      simp at a0 a1
      rw [a0, a1]; simp
    · rw [hparallel] at h3
      obtain ⟨c, hc⟩ := h3
      have a0 := congrFun hc 0
      have a1 := congrFun hc 1
      rw [h.1] at a0; rw [h.2] at a1
      simp at a0 a1
      rw [a0, a1]; ring
  have hgp : ∀ x, 0 < g x := fun x => (prop2 x).1
  have hg1 : ∀ x, x ^ 2 * g x ≤ 1 := fun x => (prop2 x).2
  have hdiag : ∀ x, F ![x, x] = 0 := fun x => prop1 _ (by simp)
  have hgc : Continuous g := Fgdiff.2.continuous
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
  simp only [hv]
  -- bounds on G
  have hφ : ∀ y : ℝ, y ≠ 0 → HasDerivAt (fun y => G y + y⁻¹) (g y - (y^2)⁻¹) y := by
    intro y hy
    have := (hG y).add (hasDerivAt_inv hy)
    refine HasDerivAt.congr_deriv this ?_; ring
  have hφn : ∀ y : ℝ, y ≠ 0 → g y - (y^2)⁻¹ ≤ 0 := by
    intro y hy
    have hy2 : 0 < y^2 := by positivity
    have : g y ≤ 1 / y^2 := by rw [le_div_iff₀ hy2]; linarith [hg1 y]
    rw [one_div] at this; linarith
  have hUp : ∀ x, G x ≤ G 1 + 1 := by
    intro x
    rcases le_total x 1 with h | h
    · have := hGm.monotone h; linarith
    · have hA : AntitoneOn (fun y => G y + y⁻¹) (Set.Ici 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
        · intro y hy
          have : y ≠ 0 := by have := hy.out; positivity
          exact (hφ y this).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Ici] at hy
          have : y ≠ 0 := by have := hy.out; positivity
          exact (hφ y this).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Ici] at hy
          have : y ≠ 0 := by have := hy.out; positivity
          rw [(hφ y this).deriv]; exact hφn y this
      have := hA (show (1:ℝ) ∈ Set.Ici 1 from Set.mem_Ici.2 le_rfl) (show x ∈ Set.Ici 1 from h) h
      have hx : 0 < x⁻¹ := inv_pos.2 (by linarith)
      simp at this; linarith
  have hLo : ∀ x, G (-1) - 1 ≤ G x := by
    intro x
    rcases le_total (-1) x with h | h
    · have := hGm.monotone h; linarith
    · have hA : AntitoneOn (fun y => G y + y⁻¹) (Set.Iic (-1)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic (-1))
        · intro y hy
          have : y ≠ 0 := by have := hy.out; intro h0; simp [h0] at this; linarith
          exact (hφ y this).continuousAt.continuousWithinAt
        · intro y hy
          rw [interior_Iic] at hy
          have : y ≠ 0 := by have := hy.out; intro h0; simp [h0] at this; linarith
          exact (hφ y this).differentiableAt.differentiableWithinAt
        · intro y hy
          rw [interior_Iic] at hy
          have : y ≠ 0 := by have := hy.out; intro h0; simp [h0] at this; linarith
          rw [(hφ y this).deriv]; exact hφn y this
      have := hA (show x ∈ Set.Iic (-1) from h) (show (-1:ℝ) ∈ Set.Iic (-1) from Set.mem_Ici.2 le_rfl) h
      have hx : x⁻¹ < 0 := inv_lt_zero.2 (by linarith)
      simp at this; linarith
  have hbA : BddAbove (Set.range G) := ⟨G 1 + 1, by rintro _ ⟨x, rfl⟩; exact hUp x⟩
  have hbB : BddBelow (Set.range G) := ⟨G (-1) - 1, by rintro _ ⟨x, rfl⟩; exact hLo x⟩
  set B := ⨆ x, G x with hB
  set A := ⨅ x, G x with hA
  have hleB : ∀ x, G x ≤ B := fun x => le_ciSup hbA x
  have hAle : ∀ x, A ≤ G x := fun x => ciInf_le hbB x
  have hltB : ∀ x, G x < B := fun x => lt_of_lt_of_le (hGm (by linarith : x < x + 1)) (hleB _)
  have hAlt : ∀ x, A < G x := fun x => lt_of_le_of_lt (hAle _) (hGm (by linarith : x - 1 < x)) |>.trans_le' le_rfl |> fun h => by
    exact lt_of_le_of_lt (hAle (x-1)) (hGm (by linarith : x - 1 < x))
  have hAB : A < B := lt_trans (hAlt 0) (hltB 0)
  obtain ⟨b0, hb0⟩ := exists_lt_of_lt_ciSup (show B - (B - A)/4 < B by linarith)
  obtain ⟨a0, ha0⟩ := exists_lt_of_ciInf_lt (show A < A + (B - A)/4 by linarith)
  have hab : a0 ≤ b0 := hGm.le_iff_le.1 (by linarith)
  set T := G b0 - G a0 with hT
  have hTgt : (B - A)/2 < T := by simp only [hT]; linarith
  -- generic Lipschitz at a0
  have hlip : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a0 = 0 → ∃ K, 0 ≤ K ∧ ∀ b ∈ Set.Icc a0 b0, |φ b| ≤ K * (b - a0) := by
    intro φ hφd h0
    have hc : Continuous (deriv φ) := hφd.continuous_deriv le_rfl
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a0) (b := b0)).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun b hb => ?_⟩
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := φ) (s := Set.Icc a0 b0) (C := C)
      (fun x _ => (hφd.differentiable one_ne_zero) x) hC (convex_Icc a0 b0)
      (show a0 ∈ Set.Icc a0 b0 from ⟨le_rfl, hab⟩) hb
    rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show (0:ℝ) ≤ b - a0 by linarith [hb.1])] at this
    calc |φ b| ≤ C * (b - a0) := this
      _ ≤ max C 0 * (b - a0) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hb.1])
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := a0) (b := b0)).exists_isMinOn (Set.nonempty_Icc.2 hab) hgc.continuousOn
  have hgm : ∀ b ∈ Set.Icc a0 b0, g x0 * (b - a0) ≤ G b - G a0 := by
    intro b hb
    rcases eq_or_lt_of_le hb.1 with h | h
    · rw [← h]; simp
    · obtain ⟨c, hc, hcg⟩ := exists_hasDerivAt_eq_slope G g h hGc.continuousOn (fun x _ => hG x)
      have h1 : g x0 ≤ g c := hmin ⟨hc.1.le, hc.2.le.trans hb.2⟩
      rw [eq_div_iff (by linarith)] at hcg
      nlinarith
  have hgm0 := hgp x0
  have hmaps : ∀ y, G a0 ≤ y → y ≤ G b0 → ∃ b ∈ Set.Icc a0 b0, G b = y :=
    fun y h1 h2 => intermediate_value_Icc hab hGc.continuousOn ⟨h1, h2⟩
  have hcd : ∀ a : ℝ, ContDiff ℝ 1 (fun w : ℝ => (![a, w] : Fin 2 → ℝ)) := fun a =>
    contDiff_pi.2 (fun i => by fin_cases i <;> simp <;> first | exact contDiff_id | exact contDiff_const)
  have hcd' : ∀ a : ℝ, ContDiff ℝ 1 (fun w : ℝ => (![w, a] : Fin 2 → ℝ)) := fun a =>
    contDiff_pi.2 (fun i => by fin_cases i <;> simp <;> first | exact contDiff_id | exact contDiff_const)
  obtain ⟨K1, hK1, hK1b⟩ := hlip (fun w => F ![a0, w]) ((hF1.of_le (by norm_num)).comp (hcd a0)) (hdiag a0)
  obtain ⟨K2, hK2, hK2b⟩ := hlip (fun w => F ![w, a0]) ((hF1.of_le (by norm_num)).comp (hcd' a0)) (hdiag a0)
  set M := max K1 K2 with hM
  set K := M / g x0 with hKdef
  have hM0 : 0 ≤ M := le_trans hK1 (le_max_left _ _)
  have hK0 : 0 ≤ K := by positivity
  have hfin : ∀ K', 0 ≤ K' → K' ≤ M → ∀ b ∈ Set.Icc a0 b0, K' * (b - a0) ≤ K * (G b - G a0) := by
    intro K' _ hK'M b hb
    have h1 : 0 ≤ b - a0 := by linarith [hb.1]
    have h2 : b - a0 ≤ (G b - G a0) / g x0 := by rw [le_div_iff₀ hgm0]; linarith [hgm b hb]
    calc K' * (b - a0) ≤ M * (b - a0) := mul_le_mul_of_nonneg_right hK'M h1
      _ ≤ M * ((G b - G a0) / g x0) := mul_le_mul_of_nonneg_left h2 hM0
      _ = K * (G b - G a0) := by rw [hKdef]; ring
  have hbound : ∀ u v, |G u - G v| ≤ T → |F ![u, v]| ≤ K * |G u - G v| := by
    intro u v huv
    rcases le_total (G u) (G v) with h | h
    · rw [abs_of_nonpos (show G u - G v ≤ 0 by linarith)] at huv ⊢
      obtain ⟨b, hb, hGb⟩ := hmaps (G a0 + (G v - G u)) (by linarith) (by simp only [hT] at huv; linarith)
      rw [hinv u v a0 b (by linarith)]
      calc |F ![a0, b]| ≤ K1 * (b - a0) := hK1b b hb
        _ ≤ K * (G b - G a0) := hfin K1 hK1 (le_max_left _ _) b hb
        _ = K * -(G u - G v) := by rw [hGb]; ring
    · rw [abs_of_nonneg (show 0 ≤ G u - G v by linarith)] at huv ⊢
      obtain ⟨b, hb, hGb⟩ := hmaps (G a0 + (G u - G v)) (by linarith) (by simp only [hT] at huv; linarith)
      rw [hinv u v b a0 (by linarith)]
      calc |F ![b, a0]| ≤ K2 * (b - a0) := hK2b b hb
        _ ≤ K * (G b - G a0) := hfin K2 hK2 (le_max_right _ _) b hb
        _ = K * (G u - G v) := by rw [hGb]; ring
  refine ⟨K * (B - A), fun n hn x => ?_⟩
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  set w := (B - A) / n with hw
  have hwpos : 0 < w := by positivity
  have hw2 : w ≤ (B - A) / 2 := by
    rw [hw]; apply div_le_div_of_nonneg_left (by linarith) (by norm_num) hn2
  have hwn : w * n = B - A := by rw [hw]; field_simp
  obtain ⟨i, -, j, -, hij, hfl⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (Fin (n+1)))) (t := Finset.range n)
    (f := fun i => ⌊(G (x i) - A) / w⌋₊) (by simp) (by
      intro i _
      rw [Finset.mem_coe, Finset.mem_range, Nat.floor_lt (div_nonneg (by linarith [hAlt (x i)]) hwpos.le), div_lt_iff₀ hwpos]
      nlinarith [hltB (x i)])
  have hfl : ⌊(G (x i) - A) / w⌋₊ = ⌊(G (x j) - A) / w⌋₊ := hfl
  have hri := Nat.floor_le (div_nonneg (by linarith [hAlt (x i)]) hwpos.le : 0 ≤ (G (x i) - A) / w)
  have hrj := Nat.floor_le (div_nonneg (by linarith [hAlt (x j)]) hwpos.le : 0 ≤ (G (x j) - A) / w)
  have hri' := Nat.lt_floor_add_one ((G (x i) - A) / w)
  have hrj' := Nat.lt_floor_add_one ((G (x j) - A) / w)
  rw [hfl] at hri hri'
  have hd : |(G (x i) - A) / w - (G (x j) - A) / w| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  have hd2 : |G (x i) - G (x j)| < w := by
    have : (G (x i) - A) / w - (G (x j) - A) / w = (G (x i) - G (x j)) / w := by ring
    rw [this, abs_div, abs_of_pos hwpos, div_lt_one hwpos] at hd
    exact hd
  have hle : |G (x i) - G (x j)| ≤ T := by linarith
  have h1 := hbound (x i) (x j) hle
  have hmem : |F ![x i, x j]| ∈ {Fxx : ℝ | ∃ i j : Fin (n + 1), i ≠ j ∧ Fxx = |F ![x i, x j]|} := ⟨i, j, hij, rfl⟩
  have hbd : BddBelow {Fxx : ℝ | ∃ i j : Fin (n + 1), i ≠ j ∧ Fxx = |F ![x i, x j]|} :=
    ⟨0, by rintro _ ⟨i, j, _, rfl⟩; exact abs_nonneg _⟩
  refine (csInf_le hbd hmem).trans ?_
  calc |F ![x i, x j]| ≤ K * |G (x i) - G (x j)| := h1
    _ ≤ K * w := mul_le_mul_of_nonneg_left hd2.le hK0
    _ = K * (B - A) / n := by rw [hw]; ring
