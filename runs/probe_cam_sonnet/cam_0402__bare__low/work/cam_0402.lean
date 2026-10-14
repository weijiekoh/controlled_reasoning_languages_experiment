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
  have hH : P.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hP_symm
  have hPSD : P.PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (by simpa using hP_psd)
  have h0 : ∀ x, dotProduct x (P.mulVec x) = 0 → P.mulVec x = 0 := fun x h =>
    (hPSD.dotProduct_mulVec_zero_iff x).1 (by simpa using h)
  have hdot : ∀ (x : Fin n → ℝ) (y : Fin p → ℝ),
      dotProduct x (Aᵀ.mulVec y) = dotProduct (A.mulVec x) y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hrk : Function.Injective Aᵀ.mulVec := by
    have h1 := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
    have h2 : Module.finrank ℝ (LinearMap.range Aᵀ.mulVecLin) = p := by
      have := Matrix.rank_transpose A
      unfold Matrix.rank at this
      rw [this]; exact hA_rank
    rw [h2, Module.finrank_fin_fun] at h1
    have h3 : Module.finrank ℝ (LinearMap.ker Aᵀ.mulVecLin) = 0 := by omega
    have h5 : LinearMap.ker Aᵀ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h3
    exact LinearMap.ker_eq_bot.1 h5
  have hc2 : cond2 ↔ ∀ x, P.mulVec x = 0 → A.mulVec x = 0 → x = 0 := by
    show _ ↔ _
    simp only [cond2, Submodule.eq_bot_iff, Submodule.mem_inf, LinearMap.mem_ker,
      Matrix.toLin'_apply, Submodule.mem_bot]
    constructor
    · intro h x h1 h2; exact h x ⟨h1, h2⟩
    · intro h x hx; exact h x hx.1 hx.2
  have h12 : cond1 ↔ cond2 := by
    rw [hc2]
    constructor
    · intro hd x h1 h2
      by_contra hx
      apply hd
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨Sum.elim x 0, ?_, ?_⟩
      · intro h; apply hx; funext i; simpa using congrFun h (Sum.inl i)
      · simp only [K]
        rw [Matrix.fromBlocks_mulVec]
        simp [h1, h2]
    · intro h hd
      obtain ⟨v, hv, hKv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
      have hv' : v = Sum.elim (fun i => v (Sum.inl i)) (fun j => v (Sum.inr j)) := by
        ext (i|j) <;> simp
      set x := fun i => v (Sum.inl i)
      set y := fun j => v (Sum.inr j)
      rw [hv'] at hKv
      simp only [K] at hKv
      rw [Matrix.fromBlocks_mulVec] at hKv
      have e1 : P.mulVec x + Aᵀ.mulVec y = 0 := by
        funext i; simpa using congrFun hKv (Sum.inl i)
      have e2 : A.mulVec x = 0 := by
        funext i; simpa using congrFun hKv (Sum.inr i)
      have e3 : dotProduct x (P.mulVec x) = 0 := by
        have := congrArg (dotProduct x) e1
        rw [dotProduct_add, hdot, e2] at this
        simpa using this
      have hx : x = 0 := h x (h0 x e3) e2
      have e4 : Aᵀ.mulVec y = 0 := by
        rw [hx] at e1; simpa using e1
      have hy : y = 0 := hrk (by rw [e4]; simp)
      apply hv
      rw [hv', hx, hy]; ext (i|j) <;> simp
  have h23 : cond2 ↔ cond3 := by
    rw [hc2]
    constructor
    · intro h x h1 h2
      rcases (hP_psd x).lt_or_eq with h3 | h3
      · exact h3
      · exact absurd (h x (h0 x h3.symm) h1) h2
    · intro h x h1 h2
      by_contra hx
      have := h x h2 hx
      rw [h1] at this; simp at this
  have hFinj : ∀ F : Matrix (Fin n) (Fin (n - p)) ℝ,
      LinearMap.range F.toLin' = LinearMap.ker A.toLin' → Function.Injective F.mulVec := by
    intro F hF
    have h1 := LinearMap.finrank_range_add_finrank_ker A.toLin'
    have h2 : Module.finrank ℝ (LinearMap.range A.toLin') = p := by
      exact hA_rank
    have h3 := LinearMap.finrank_range_add_finrank_ker F.toLin'
    rw [hF] at h3
    simp at h1 h3
    have : Module.finrank ℝ (LinearMap.ker F.toLin') = 0 := by omega
    have h5 : LinearMap.ker F.toLin' = ⊥ := Submodule.finrank_eq_zero.1 this
    exact LinearMap.ker_eq_bot.1 h5
  have hFe : ∀ (F : Matrix (Fin n) (Fin (n - p)) ℝ) (v : Fin (n - p) → ℝ),
      dotProduct v ((Fᵀ * P * F).mulVec v) = dotProduct (F.mulVec v) (P.mulVec (F.mulVec v)) := by
    intro F v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h34 : cond3 ↔ cond4 := by
    constructor
    · intro h F hF
      have hinj := hFinj F hF
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · simp only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
          Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
        rw [hP_symm]
      · intro v hv
        have hFv : F.mulVec v ≠ 0 := by
          intro h'; apply hv; apply hinj; rw [h']; simp
        have hmem : F.mulVec v ∈ LinearMap.ker A.toLin' := by
          rw [← hF]; exact ⟨v, by simp [Matrix.toLin'_apply]⟩
        have hA0 : A.mulVec (F.mulVec v) = 0 := by simpa [Matrix.toLin'_apply] using hmem
        have := h _ hA0 hFv
        simp only [star_trivial]
        rw [hFe]
        exact this
    · intro h x hx hx0
      obtain ⟨F, hF⟩ : ∃ F : Matrix (Fin n) (Fin (n - p)) ℝ,
          LinearMap.range F.toLin' = LinearMap.ker A.toLin' := by
        have h1 := LinearMap.finrank_range_add_finrank_ker A.toLin'
        have h2 : Module.finrank ℝ (LinearMap.range A.toLin') = p := by
          exact hA_rank
        have hd : Module.finrank ℝ (LinearMap.ker A.toLin') = n - p := by
          simp at h1 h2 ⊢; omega
        have e : (Fin (n - p) → ℝ) ≃ₗ[ℝ] LinearMap.ker A.toLin' :=
          LinearEquiv.ofFinrankEq _ _ (by simp [hd])
        refine ⟨LinearMap.toMatrix' ((LinearMap.ker A.toLin').subtype ∘ₗ e.toLinearMap), ?_⟩
        rw [Matrix.toLin'_toMatrix', LinearMap.range_comp]
        simp
      have hxm : x ∈ LinearMap.range F.toLin' := by
        rw [hF]; simpa [Matrix.toLin'_apply] using hx
      obtain ⟨v, hv⟩ := hxm
      have hv' : F.mulVec v = x := by simpa [Matrix.toLin'_apply] using hv
      have hv0 : v ≠ 0 := by rintro rfl; apply hx0; rw [← hv']; simp
      have h6 := (h F hF).dotProduct_mulVec_pos hv0
      simp only [star_trivial] at h6
      rw [hFe F v, hv'] at h6
      exact h6
  have h35 : cond3 ↔ cond5 := by
    constructor
    · intro h
      refine ⟨(1 : Matrix (Fin p) (Fin p) ℝ), ?_, ?_, ?_⟩
      · simp [Matrix.IsSymm]
      · intro y; simpa using dotProduct_self_star_nonneg y
      · have key : ∀ x : Fin n → ℝ, dotProduct x ((P + Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A).mulVec x)
            = dotProduct x (P.mulVec x) + dotProduct (A.mulVec x) (A.mulVec x) := by
          intro x
          simp [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, hdot]
        apply Matrix.PosDef.of_dotProduct_mulVec_pos
        · simp only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
            Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
            Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
          rw [hP_symm]
        · intro x hx
          simp only [star_trivial]
          rw [key]
          have a1 := hP_psd x
          have a2 : 0 ≤ dotProduct (A.mulVec x) (A.mulVec x) := by
            simpa using dotProduct_self_star_nonneg (A.mulVec x)
          by_cases hA : A.mulVec x = 0
          · have := h x hA hx; rw [hA]; simpa using this
          · have : 0 < dotProduct (A.mulVec x) (A.mulVec x) := by
              rcases a2.lt_or_eq with h' | h'
              · exact h'
              · exact absurd (dotProduct_self_eq_zero.1 h'.symm) hA
            linarith
    · rintro ⟨Q, hQs, hQ, hpd⟩ x hx hx0
      have := hpd.dotProduct_mulVec_pos hx0
      simp only [star_trivial] at this
      have e : dotProduct x ((P + Aᵀ * Q * A).mulVec x)
          = dotProduct x (P.mulVec x) + dotProduct (A.mulVec x) (Q.mulVec (A.mulVec x)) := by
        simp [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, hdot]
      rw [e, hx] at this
      simpa using this
  exact ⟨h12, h12.trans h23, (h12.trans h23).trans h34, (h12.trans h23).trans h35⟩

end «CAM-Bench-402»
