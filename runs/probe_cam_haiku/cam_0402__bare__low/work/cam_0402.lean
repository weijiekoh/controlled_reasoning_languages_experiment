import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-402»

theorem kkt_matrix_nonsingular_iff_conditions
    {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (hP_symm : P.IsSymm) (hP_psd : ∀ x : Fin n → ℝ, 0 ≤ dotProduct x (P.mulVec x))
    (hA_rank : Matrix.rank A = p) (hpn : p < n) :
    let K := Matrix.fromBlocks P Aᵀ A (0 : Matrix (Fin p) (Fin p) ℝ)
    let cond1 : Prop := K.det ≠ 0
    let cond2 : Prop :=
      ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
        (LinearMap.ker A.toLin' : Submodule ℝ (Fin n → ℝ)) = ⊥)
    let cond3 : Prop :=
      ∀ x : Fin n → ℝ, A.mulVec x = 0 → x ≠ 0 → 0 < dotProduct x (P.mulVec x)
    let cond4 : Prop :=
      ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
        LinearMap.range F.toLin' = LinearMap.ker A.toLin' →
        Matrix.PosDef (Fᵀ * P * F)
    let cond5 : Prop :=
      ∃ Q : Matrix (Fin p) (Fin p) ℝ,
        Q.IsSymm ∧
        (∀ y : Fin p → ℝ, 0 ≤ dotProduct y (Q.mulVec y)) ∧
        Matrix.PosDef (P + Aᵀ * Q * A)
    (cond1 ↔ cond2) ∧
    (cond1 ↔ cond3) ∧
    (cond1 ↔ cond4) ∧
    (cond1 ↔ cond5) := by
  intro K cond1 cond2 cond3 cond4 cond5
  have hinj : ∀ (a b : ℕ) (M : Matrix (Fin a) (Fin b) ℝ), Matrix.rank M = b →
      ∀ y, M *ᵥ y = 0 → y = 0 := by
    intro a b M hM y hy
    have h1 := LinearMap.finrank_range_add_finrank_ker M.toLin'
    have h2 : Matrix.rank M = Module.finrank ℝ (LinearMap.range M.toLin') := rfl
    rw [Module.finrank_fin_fun] at h1
    rw [h2] at hM
    have h3 : Module.finrank ℝ (LinearMap.ker M.toLin') = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h3
    have hy' : y ∈ LinearMap.ker M.toLin' := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hy
    rw [h3, Submodule.mem_bot] at hy'
    exact hy'
  have hnn : ∀ {m : ℕ} (v : Fin m → ℝ), 0 ≤ dotProduct v v := by
    intro m v
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hPs : Pᵀ = P := hP_symm
  have hvm : ∀ u : Fin n → ℝ, u ᵥ* P = P *ᵥ u := fun u => by
    conv_lhs => rw [← hPs]
    exact Matrix.vecMul_transpose P u
  have hsym : ∀ u w : Fin n → ℝ, dotProduct u (P *ᵥ w) = dotProduct w (P *ᵥ u) := by
    intro u w
    rw [Matrix.dotProduct_mulVec, hvm, dotProduct_comm]
  have hz : ∀ x : Fin n → ℝ, dotProduct x (P *ᵥ x) = 0 → P *ᵥ x = 0 := by
    intro x hx
    obtain ⟨v, hv⟩ : ∃ v, v = P *ᵥ x := ⟨_, rfl⟩
    rw [← hv] at hx ⊢
    have hx2 : dotProduct x v = 0 := hx
    have hb : 0 ≤ dotProduct v (P *ᵥ v) := hP_psd v
    have ha0 : 0 ≤ dotProduct v v := hnn v
    have hxv : dotProduct x (P *ᵥ v) = dotProduct v v := by rw [hsym, ← hv]
    have hquad : ∀ t : ℝ, 0 ≤ 2*t*(dotProduct v v) + t^2*(dotProduct v (P *ᵥ v)) := by
      intro t
      have h := hP_psd (x + t • v)
      have e : dotProduct (x + t•v) (P *ᵥ (x + t•v)) =
          2*t*(dotProduct v v) + t^2*(dotProduct v (P *ᵥ v)) := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
          dotProduct_smul, smul_dotProduct, smul_eq_mul, hxv, ← hv, hx2]
        ring
      rw [e] at h
      exact h
    have ha : dotProduct v v = 0 := by
      by_contra ha
      have hapos : 0 < dotProduct v v := lt_of_le_of_ne ha0 (Ne.symm ha)
      have hb1 : 0 < dotProduct v (P *ᵥ v) + 1 := by linarith
      have key := hquad (-(dotProduct v v / (dotProduct v (P *ᵥ v) + 1)))
      have e2 : 2 * (-(dotProduct v v / (dotProduct v (P *ᵥ v) + 1))) * (dotProduct v v)
          + (-(dotProduct v v / (dotProduct v (P *ᵥ v) + 1)))^2 * (dotProduct v (P *ᵥ v))
          = -(dotProduct v v)^2 * (dotProduct v (P *ᵥ v) + 2) / (dotProduct v (P *ᵥ v) + 1)^2 := by
        field_simp
        ring
      rw [e2] at key
      have : -(dotProduct v v)^2 * (dotProduct v (P *ᵥ v) + 2) / (dotProduct v (P *ᵥ v) + 1)^2 < 0 := by
        apply div_neg_of_neg_of_pos
        · have : 0 < (dotProduct v v)^2 := by positivity
          nlinarith
        · positivity
      linarith
    exact dotProduct_self_eq_zero.1 ha
  have hid : ∀ (a b : ℕ) (M : Matrix (Fin a) (Fin a) ℝ) (F : Matrix (Fin a) (Fin b) ℝ) (y : Fin b → ℝ),
      dotProduct y ((Fᵀ * M * F) *ᵥ y) = dotProduct (F *ᵥ y) (M *ᵥ (F *ᵥ y)) := by
    intro a b M F y
    have h : (Fᵀ * M * F) *ᵥ y = Fᵀ *ᵥ (M *ᵥ (F *ᵥ y)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hkerA : Module.finrank ℝ (LinearMap.ker A.toLin') = n - p := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.toLin'
    have h2 : Matrix.rank A = Module.finrank ℝ (LinearMap.range A.toLin') := rfl
    rw [Module.finrank_fin_fun] at h1
    rw [h2] at hA_rank
    omega
  have hKv : ∀ v : Fin n ⊕ Fin p → ℝ, K *ᵥ v = 0 ↔
      (P *ᵥ (fun i => v (Sum.inl i)) + Aᵀ *ᵥ (fun j => v (Sum.inr j)) = 0 ∧
        A *ᵥ (fun i => v (Sum.inl i)) = 0) := by
    intro v
    constructor
    · intro h
      constructor
      · funext i
        have := congrFun h (Sum.inl i)
        simpa [K, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type] using this
      · funext i
        have := congrFun h (Sum.inr i)
        simpa [K, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type] using this
    · rintro ⟨h1, h2⟩
      funext s
      rcases s with i | j
      · have := congrFun h1 i
        simp [K, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type] at this ⊢
        simpa [Matrix.mulVec, dotProduct] using this
      · have := congrFun h2 j
        simp [K, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type] at this ⊢
        simpa [Matrix.mulVec, dotProduct] using this
  -- cond1 ↔ cond2
  have h12 : cond1 ↔ cond2 := by
    constructor
    · intro hdet
      show (LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
        (LinearMap.ker A.toLin') = ⊥
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx1' : P *ᵥ x = 0 := hx1
      have hx2' : A *ᵥ x = 0 := hx2
      by_contra hne
      apply hdet
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨Sum.elim x 0, ?_, ?_⟩
      · intro h
        apply hne
        funext i
        simpa using congrFun h (Sum.inl i)
      · rw [hKv]
        have h0 : (fun j : Fin p => (Sum.elim x 0 : Fin n ⊕ Fin p → ℝ) (Sum.inr j)) = 0 :=
          funext fun j => rfl
        have h1 : (fun i : Fin n => (Sum.elim x 0 : Fin n ⊕ Fin p → ℝ) (Sum.inl i)) = x :=
          funext fun i => rfl
        rw [h0, h1, Matrix.mulVec_zero, add_zero]
        exact ⟨hx1', hx2'⟩
    · intro hc2 hdet
      have hc2' : (LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
          (LinearMap.ker A.toLin') = ⊥ := hc2
      obtain ⟨v, hv, hKv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      rw [hKv] at hKv0
      obtain ⟨h1, h2⟩ := hKv0
      have hxP : dotProduct (fun i => v (Sum.inl i))
          (P *ᵥ (fun i => v (Sum.inl i))) = 0 := by
        have : P *ᵥ (fun i => v (Sum.inl i)) = -(Aᵀ *ᵥ (fun j => v (Sum.inr j))) :=
          eq_neg_of_add_eq_zero_left h1
        rw [this, dotProduct_neg, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, h2,
          zero_dotProduct, neg_zero]
      have hPx0 := hz _ hxP
      have hx0 : (fun i => v (Sum.inl i)) = 0 := by
        have hmem : (fun i => v (Sum.inl i)) ∈
            ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
              (LinearMap.ker A.toLin')) := by
          rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
          exact ⟨hPx0, h2⟩
        rw [hc2', Submodule.mem_bot] at hmem
        exact hmem
      have hAy : Aᵀ *ᵥ (fun j => v (Sum.inr j)) = 0 := by
        have h0 : P *ᵥ (fun i => v (Sum.inl i)) = 0 := by
          rw [hx0]; exact Matrix.mulVec_zero _
        rw [h0, zero_add] at h1
        exact h1
      have hy0 := hinj n p Aᵀ (by rw [Matrix.rank_transpose]; exact hA_rank) _ hAy
      apply hv
      funext s
      rcases s with i | j
      · exact congrFun hx0 i
      · exact congrFun hy0 j
  -- cond2 ↔ cond3
  have h23 : cond2 ↔ cond3 := by
    constructor
    · intro h x hAx hx
      have h2 : (LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
          (LinearMap.ker A.toLin') = ⊥ := h
      rcases lt_or_eq_of_le (hP_psd x) with h' | h'
      · exact h'
      · exfalso
        have hPx := hz x h'.symm
        have hmem : x ∈ ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
            (LinearMap.ker A.toLin')) := by
          rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
          exact ⟨hPx, hAx⟩
        rw [h2, Submodule.mem_bot] at hmem
        exact hx hmem
    · intro h
      have h2 : (LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
          (LinearMap.ker A.toLin') = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
        obtain ⟨hx1, hx2⟩ := hx
        have hx1' : P *ᵥ x = 0 := hx1
        have hx2' : A *ᵥ x = 0 := hx2
        by_contra hne
        have := h x hx2' hne
        rw [hx1', dotProduct_zero] at this
        exact lt_irrefl _ this
      exact h2
  -- existence of F
  have hexF : ∃ F : Matrix (Fin n) (Fin (n - p)) ℝ,
      LinearMap.range F.toLin' = LinearMap.ker A.toLin' := by
    let kA := LinearMap.ker A.toLin'
    let e : (Fin (n - p) → ℝ) ≃ₗ[ℝ] kA :=
      LinearEquiv.ofFinrankEq _ _ (by rw [Module.finrank_fin_fun, hkerA])
    refine ⟨LinearMap.toMatrix' (kA.subtype ∘ₗ e.toLinearMap), ?_⟩
    rw [Matrix.toLin'_toMatrix']
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).2
    · intro hz'
      exact ⟨e.symm ⟨z, hz'⟩, by simp⟩
  have hrankF : ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
      LinearMap.range F.toLin' = LinearMap.ker A.toLin' → Matrix.rank F = n - p := by
    intro F hF
    show Module.finrank ℝ (LinearMap.range F.toLin') = n - p
    rw [hF, hkerA]
  -- cond3 ↔ cond4
  have h34 : cond3 ↔ cond4 := by
    constructor
    · intro h3 F hF
      have hrF := hrankF F hF
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨?_, fun y hy => ?_⟩
      · unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_eq_transpose_of_trivial]
        simp [Matrix.transpose_mul, hPs, Matrix.mul_assoc]
      · have hFy : F *ᵥ y ≠ 0 := fun h0 => hy (hinj n (n - p) F hrF y h0)
        have hmem : F *ᵥ y ∈ LinearMap.ker A.toLin' := by
          rw [← hF]; exact LinearMap.mem_range.2 ⟨y, rfl⟩
        have hAFy : A *ᵥ (F *ᵥ y) = 0 := hmem
        show 0 < dotProduct y ((Fᵀ * P * F) *ᵥ y)
        rw [hid]
        exact h3 _ hAFy hFy
    · intro h4 x hAx hx
      obtain ⟨F, hF⟩ := hexF
      have hpd := h4 F hF
      rw [Matrix.posDef_iff_dotProduct_mulVec] at hpd
      have hxr : x ∈ LinearMap.range F.toLin' := by
        rw [hF]; exact LinearMap.mem_ker.2 hAx
      obtain ⟨y, hy⟩ := hxr
      have hFy : F *ᵥ y = x := hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        apply hx
        rw [← hFy, Matrix.mulVec_zero]
      have h' : 0 < dotProduct y ((Fᵀ * P * F) *ᵥ y) := hpd.2 hy0
      rw [hid, hFy] at h'
      exact h'
  -- cond2 ↔ cond5
  have h25 : cond2 ↔ cond5 := by
    constructor
    · intro hc2
      simp only [cond5]
      have hc2' : (LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
          (LinearMap.ker A.toLin') = ⊥ := hc2
      obtain ⟨g, hgdef⟩ : ∃ g : (Fin n → ℝ) → ℝ,
          g = fun x => dotProduct x (P *ᵥ x) + dotProduct (A *ᵥ x) (A *ᵥ x) := ⟨_, rfl⟩
      have hgapp : ∀ x, g x = dotProduct x (P *ᵥ x) + dotProduct (A *ᵥ x) (A *ᵥ x) :=
        fun x => by rw [hgdef]
      have hcont : Continuous g := by
        rw [hgdef]; unfold dotProduct; fun_prop
      have hg : ∀ (c : ℝ) (x : Fin n → ℝ), g (c • x) = c^2 * g x := by
        intro c x
        rw [hgapp, hgapp]
        simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
        ring
      have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
        haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
        exact NormedSpace.sphere_nonempty.mpr zero_le_one
      obtain ⟨x0, hx0S, hmin⟩ :=
        (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne hcont.continuousOn
      have hx0n : ‖x0‖ = 1 := by simpa using hx0S
      have hx0ne : x0 ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx0n
        norm_num at hx0n
      have hgx0 : 0 < g x0 := by
        by_contra hle
        push_neg at hle
        have h1 : dotProduct x0 (P *ᵥ x0) = 0 :=
          le_antisymm (by linarith [hP_psd x0, hnn (A *ᵥ x0), hgapp x0]) (hP_psd x0)
        have h2 : dotProduct (A *ᵥ x0) (A *ᵥ x0) = 0 :=
          le_antisymm (by linarith [hP_psd x0, hnn (A *ᵥ x0), hgapp x0]) (hnn _)
        have hAx0 : A *ᵥ x0 = 0 := dotProduct_self_eq_zero.1 h2
        have hPx0 := hz x0 h1
        have hmem : x0 ∈ ((LinearMap.ker P.toLin' : Submodule ℝ (Fin n → ℝ)) ⊓
            (LinearMap.ker A.toLin')) := by
          rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
          exact ⟨hPx0, hAx0⟩
        rw [hc2', Submodule.mem_bot] at hmem
        exact hx0ne hmem
      have hherm : (P + Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A).IsHermitian := by
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_eq_transpose_of_trivial]
        simp [Matrix.transpose_mul, hPs, Matrix.mul_assoc]
      refine ⟨1, ?_, fun y => ?_, ?_⟩
      · unfold Matrix.IsSymm; simp
      · rw [Matrix.one_mulVec]; exact hnn y
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨hherm, fun y hy => ?_⟩
      · have hs : 0 < ‖y‖ := norm_pos_iff.2 hy
        have hz1 : ‖(‖y‖⁻¹) • y‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
        have hmz := isMinOn_iff.1 hmin _ (by rw [mem_sphere_zero_iff_norm]; exact hz1)
        have hyeq : y = ‖y‖ • (‖y‖⁻¹ • y) := by
          rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
        have hgy : g y = ‖y‖^2 * g (‖y‖⁻¹ • y) := by
          conv_lhs => rw [hyeq]
          exact hg _ _
        have hpos : 0 < g y := by
          rw [hgy]; exact mul_pos (by positivity) (lt_of_lt_of_le hgx0 hmz)
        have hq : dotProduct y ((Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A) *ᵥ y) =
            dotProduct (A *ᵥ y) (A *ᵥ y) := by
          rw [Matrix.mul_one, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            Matrix.vecMul_transpose]
        have key : dotProduct y ((P + Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A) *ᵥ y) = g y := by
          rw [hgapp, Matrix.add_mulVec, dotProduct_add, hq]
        show 0 < dotProduct y ((P + Aᵀ * 1 * A) *ᵥ y)
        rw [key]
        exact hpos
    · intro h5
      simp only [cond5] at h5
      obtain ⟨Q, hQs, hQp, hPD⟩ := h5
      simp only [cond2]
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx1' : P *ᵥ x = 0 := hx1
      have hx2' : A *ᵥ x = 0 := hx2
      by_contra hne
      have h' : 0 < dotProduct x ((P + Aᵀ * Q * A) *ᵥ x) :=
        (Matrix.posDef_iff_dotProduct_mulVec.1 hPD).2 hne
      simp [Matrix.add_mulVec, dotProduct_add, hid, hx2', hx1'] at h'
  have h12' := h12.trans h23
  exact ⟨h12, h12', h12'.trans h34, h12.trans h25⟩

end «CAM-Bench-402»
