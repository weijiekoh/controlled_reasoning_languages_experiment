import Mathlib

open Real Set Nat

noncomputable abbrev putnam_2016_b4_solution : ℕ → ℝ := (fun n : ℕ => (2 * n)! / (4 ^ n * (n)!))


def vv (b : Bool) : ℝ := if b then 1 else 0

lemma two_coord {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι) (hpq : p ≠ q)
    (ph : Bool → Bool → ℝ) (G : (ι → Bool) → ℝ)
    (hG : ∀ f b c, G (Function.update (Function.update f p b) q c) = G f) :
    ∑ f, ph (f p) (f q) * G f = (1/4) * (∑ b, ∑ c, ph b c) * ∑ f, G f := by
  have hN : ∀ b c : Bool, ∑ f : ι → Bool, (if f p = b ∧ f q = c then G f else 0)
      = ∑ f : ι → Bool, (if f p = false ∧ f q = false then G f else 0) := by
    intro b c
    let ψ : (ι → Bool) → (ι → Bool) := fun f => Function.update (Function.update f p (xor (f p) b)) q (xor (f q) c)
    have hψ : ∀ f, ψ (ψ f) = f := by
      intro f; funext x
      by_cases hxq : x = q
      · subst hxq; simp [ψ, Function.update, hpq.symm]
      · by_cases hxp : x = p
        · subst hxp; simp [ψ, Function.update, hxq]
        · simp [ψ, Function.update, hxq, hxp]
    let e : (ι → Bool) ≃ (ι → Bool) := ⟨ψ, ψ, hψ, hψ⟩
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro f _
    have h1 : e f p = xor (f p) b := by simp [e, ψ, Function.update, hpq]
    have h2 : e f q = xor (f q) c := by simp [e, ψ, Function.update]
    have h3 : G (e f) = G f := hG f _ _
    rw [h1, h2, h3]
    cases b <;> cases c <;> cases hp : f p <;> cases hq : f q <;> simp
  have hsum : ∑ f, G f = 4 * ∑ f : ι → Bool, (if f p = false ∧ f q = false then G f else 0) := by
    have : ∀ f, G f = ∑ b, ∑ c, (if f p = b ∧ f q = c then G f else 0) := by
      intro f
      cases hp : f p <;> cases hq : f q <;> simp
    calc ∑ f, G f = ∑ f, ∑ b, ∑ c, (if f p = b ∧ f q = c then G f else 0) :=
          Finset.sum_congr rfl (fun f _ => this f)
      _ = ∑ b, ∑ c, ∑ f : ι → Bool, (if f p = b ∧ f q = c then G f else 0) := by
          rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
          rw [Finset.sum_comm]
      _ = _ := by
          simp only [hN]; simp; ring
  have : ∀ f : ι → Bool, ph (f p) (f q) * G f = ∑ b, ∑ c, ph b c * (if f p = b ∧ f q = c then G f else 0) := by
    intro f
    cases hp : f p <;> cases hq : f q <;> simp
  calc ∑ f, ph (f p) (f q) * G f = ∑ f, ∑ b, ∑ c, ph b c * (if f p = b ∧ f q = c then G f else 0) :=
        Finset.sum_congr rfl (fun f _ => this f)
    _ = ∑ b, ∑ c, ph b c * ∑ f : ι → Bool, (if f p = b ∧ f q = c then G f else 0) := by
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _
        rw [Finset.mul_sum]
    _ = _ := by
        simp only [hN, hsum, ← Finset.sum_mul, ← Finset.sum_mul]
        simp [← Finset.sum_mul]; ring_nf

def hh {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) (f : Fin m × Fin m → Bool) : ℝ :=
  vv (f (σ i, i)) - vv (f (i, σ i))

lemma inv_case {m : ℕ} (σ : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (σ i) = i) (hf : ∀ i, σ i ≠ i) :
    ∀ k : ℕ, ∀ s : Finset (Fin m), s.card = 2 * k → (∀ i ∈ s, σ i ∈ s) →
      ∑ f : Fin m × Fin m → Bool, ∏ i ∈ s, hh σ i f = 2 ^ (m * m) * (-1/2 : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
    intro s hs _
    have : s = ∅ := Finset.card_eq_zero.mp (by simpa using hs)
    subst this
    simp
  | succ k ih =>
    intro s hs hcl
    have hne : s.Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨i, hi⟩ := hne
    have hσi : σ i ∈ s.erase i := Finset.mem_erase.mpr ⟨hf i, hcl i hi⟩
    set s' := (s.erase i).erase (σ i) with hs'
    have hcard : s'.card = 2 * k := by
      rw [hs', Finset.card_erase_of_mem hσi, Finset.card_erase_of_mem hi]; omega
    have hmem : ∀ j ∈ s', j ≠ i ∧ j ≠ σ i ∧ σ j ≠ i ∧ σ j ≠ σ i := by
      intro j hj
      simp only [hs', Finset.mem_erase] at hj
      obtain ⟨h1, h2, h3⟩ := hj
      refine ⟨h2, h1, ?_, ?_⟩
      · intro h; apply h1; rw [← h, hσ]
      · intro h; apply h2; exact σ.injective h
    have hcl' : ∀ j ∈ s', σ j ∈ s' := by
      intro j hj
      obtain ⟨a, b, c, d⟩ := hmem j hj
      simp only [hs', Finset.mem_erase]
      exact ⟨d, c, hcl j (by simp only [hs', Finset.mem_erase] at hj; exact hj.2.2)⟩
    have hprod : ∀ f, ∏ j ∈ s, hh σ j f = (hh σ i f * hh σ (σ i) f) * ∏ j ∈ s', hh σ j f := by
      intro f
      rw [← Finset.mul_prod_erase s _ hi, ← Finset.mul_prod_erase (s.erase i) _ hσi, mul_assoc]
    have hpq : ((i, σ i) : Fin m × Fin m) ≠ (σ i, i) := by
      intro h; exact hf i (Prod.mk.inj h).1.symm
    have key := two_coord (i, σ i) (σ i, i) hpq
      (fun b c => (vv c - vv b) * (vv b - vv c))
      (fun f => ∏ j ∈ s', hh σ j f) (by
        intro f b c
        apply Finset.prod_congr rfl
        intro j hj
        obtain ⟨a1, a2, a3, a4⟩ := hmem j hj
        unfold hh
        rw [Function.update_of_ne, Function.update_of_ne, Function.update_of_ne, Function.update_of_ne]
        all_goals simp [Prod.ext_iff, *, Ne.symm]
        )
    simp only [hprod]
    have e1 : ∀ f : Fin m × Fin m → Bool, (hh σ i f * hh σ (σ i) f) =
        (fun b c => (vv c - vv b) * (vv b - vv c)) (f (i, σ i)) (f (σ i, i)) := by
      intro f; simp [hh, hσ]
    simp only [e1]
    rw [key, ih s' hcard hcl']
    have : ∑ b : Bool, ∑ c : Bool, (vv c - vv b) * (vv b - vv c) = -2 := by
      simp [vv]; norm_num
    rw [this]
    rw [pow_succ]; ring

lemma zero_case {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : ¬ (∀ i, σ (σ i) = i ∧ σ i ≠ i)) :
    ∑ f : Fin m × Fin m → Bool, ∏ i, hh σ i f = 0 := by
  by_cases hfix : ∃ i, σ i = i
  · obtain ⟨i, hi⟩ := hfix
    apply Finset.sum_eq_zero; intro f _
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hh, hi]
  · push_neg at hfix
    have : ∃ i, σ (σ i) ≠ i := by
      by_contra hc; push_neg at hc
      exact h (fun i => ⟨hc i, hfix i⟩)
    obtain ⟨i, hi⟩ := this
    set p : Fin m × Fin m := (i, σ i)
    set q : Fin m × Fin m := (σ i, i)
    let e : (Fin m × Fin m → Bool) ≃ (Fin m × Fin m → Bool) :=
      Equiv.arrowCongr (Equiv.swap p q) (Equiv.refl Bool)
    have he : ∀ f x, e f x = f (Equiv.swap p q x) := by
      intro f x; simp [e, Equiv.arrowCongr, Equiv.symm_swap]
    have hother : ∀ j, j ≠ i → ∏ _x ∈ ({j} : Finset (Fin m)), (1:ℝ) = 1 := by intros; simp
    have hj' : ∀ f, ∀ j, j ≠ i → hh σ j (e f) = hh σ j f := by
      intro f j hji
      unfold hh
      rw [he, he]
      have a1 : Equiv.swap p q (σ j, j) = (σ j, j) := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; simp only [p, Prod.ext_iff] at h
          apply hi; rw [← h.2]; exact h.1
        · intro h; simp only [q, Prod.ext_iff] at h
          exact hji h.2
      have a2 : Equiv.swap p q (j, σ j) = (j, σ j) := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; simp only [p, Prod.ext_iff] at h
          exact hji h.1
        · intro h; simp only [q, Prod.ext_iff] at h
          apply hi; rw [← h.1]; exact h.2
      rw [a1, a2]
    have hi' : ∀ f, hh σ i (e f) = - hh σ i f := by
      intro f
      unfold hh
      rw [he, he]
      have hpq : p ≠ q := by
        intro h; simp only [p, q, Prod.ext_iff] at h; exact hfix i h.1.symm
      have a1 : Equiv.swap p q (σ i, i) = p := Equiv.swap_apply_right p q
      have a2 : Equiv.swap p q (i, σ i) = q := Equiv.swap_apply_left p q
      rw [a1, a2]; simp only [p, q]; ring
    have hprod : ∀ f, ∏ j, hh σ j (e f) = - ∏ j, hh σ j f := by
      intro f
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← Finset.mul_prod_erase _ (fun j => hh σ j f) (Finset.mem_univ i), hi']
      rw [Finset.prod_congr rfl (fun j hj => hj' f j (Finset.ne_of_mem_erase hj))]
      ring
    have := Equiv.sum_comp e (fun f => ∏ j, hh σ j f)
    simp only [hprod, Finset.sum_neg_distrib] at this
    linarith

lemma char_inv (n : ℕ) (σ : Equiv.Perm (Fin (2*n))) :
    (∀ i, σ (σ i) = i ∧ σ i ≠ i) ↔ σ.cycleType = Multiset.replicate n 2 := by
  constructor
  · intro h
    have hsq : σ ^ 2 = 1 := by
      ext i; simp [pow_two, Equiv.Perm.mul_apply, (h i).1]
    have hsupp : σ.support = Finset.univ := by
      ext i; simp [Equiv.Perm.mem_support, (h i).2]
    have hall : ∀ b ∈ σ.cycleType, b = 2 := by
      intro b hb
      have h1 := Equiv.Perm.dvd_of_mem_cycleType hb
      have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      have := Equiv.Perm.two_le_of_mem_cycleType hb
      have := Nat.le_of_dvd (by norm_num) (h1.trans h2)
      omega
    have e := Multiset.eq_replicate_of_mem hall
    have hs := Equiv.Perm.sum_cycleType σ
    rw [hsupp, e] at hs
    simp at hs
    rw [e]
    have : σ.cycleType.card = n := by omega
    rw [this]
  · intro h
    have hs := Equiv.Perm.sum_cycleType σ
    rw [h] at hs
    simp at hs
    have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      simp; omega
    have hlcm := Equiv.Perm.lcm_cycleType σ
    rw [h] at hlcm
    have hord : orderOf σ ∣ 2 := by
      rw [← hlcm]; 
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · apply Multiset.lcm_dvd.mpr; intro b hb; rw [Multiset.eq_of_mem_replicate hb]
    intro i
    have hi : i ∈ σ.support := by rw [hsupp]; simp
    refine ⟨?_, (Equiv.Perm.mem_support.mp hi)⟩
    have : σ ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
    have := congrArg (fun g => g i) this
    simpa [pow_two, Equiv.Perm.mul_apply] using this

lemma count_inv (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card
      * (2 ^ n * n.factorial) = (2 * n).factorial := by
  have := Equiv.Perm.card_of_cycleType_mul_eq (Fin (2*n)) (Multiset.replicate n 2)
  have h2 : (Multiset.replicate n 2).toFinset = {2} := by
    rw [Multiset.toFinset_replicate]; simp; omega
  simp [h2] at this
  rw [if_pos ⟨by omega, fun a ha => by rw [Multiset.eq_of_mem_replicate ha]⟩, show 2 * n - n * 2 = 0 by omega] at this
  simpa using this

def Mf {m : ℕ} (f : Fin m × Fin m → Bool) : Matrix (Fin m) (Fin m) ℝ := fun i j => vv (f (i, j))

lemma sumdet (n : ℕ) (hn : 1 ≤ n) :
    (∑ f : Fin (2*n) × Fin (2*n) → Bool, (Mf f - (Mf f).transpose).det) =
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card : ℝ)
        * (2 ^ ((2*n) * (2*n)) * (1/2 : ℝ) ^ n) := by
  have h1 : ∀ f : Fin (2*n) × Fin (2*n) → Bool, (Mf f - (Mf f).transpose).det =
      ∑ σ : Equiv.Perm (Fin (2*n)), (σ.sign : ℝ) * ∏ i, hh σ i f := by
    intro f
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl; intro σ _
    simp [Units.smul_def, zsmul_eq_mul, hh, Mf, Matrix.sub_apply]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ σ : Equiv.Perm (Fin (2*n)), (σ.sign : ℝ) * ∑ f : Fin (2*n) × Fin (2*n) → Bool, ∏ i, hh σ i f
      = if σ.cycleType = Multiset.replicate n 2 then 2 ^ ((2*n) * (2*n)) * (1/2 : ℝ) ^ n else 0 := by
    intro σ
    split_ifs with hc
    · have hP := (char_inv n σ).mpr hc
      rw [inv_case σ (fun i => (hP i).1) (fun i => (hP i).2) n Finset.univ (by simp [two_mul]) (by simp)]
      have : (σ.sign : ℝ) = (-1) ^ n := by
        rw [Equiv.Perm.sign_of_cycleType, hc]
        simp
        rw [pow_add, pow_mul]; simp; exact neg_one_pow_eq_or ℝ n
      rw [this]
      have : ((-1:ℝ)^n) * (-1/2)^n = (1/2)^n := by
        rw [← mul_pow]; norm_num
      calc (-1:ℝ)^n * (2 ^ ((2*n)*(2*n)) * (-1/2)^n) = 2 ^ ((2*n)*(2*n)) * ((-1:ℝ)^n * (-1/2)^n) := by ring
        _ = _ := by rw [this]
    · rw [zero_case σ, mul_zero]
      intro hP; exact hc ((char_inv n σ).mp hP)
  simp only [h2]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero]
  simp
/--
Let $A$ be a $2n \times 2n$ matrix, with entries chosen independently at random. Every entry is chosen to be $0$ or $1$, each with probability $1/2$. Find the expected value of $\det(A-A^t)$ (as a function of $n$), where $A^t$ is the transpose of $A$.
-/
theorem putnam_2016_b4
  (n : ℕ) (npos : n ≥ 1)
  (mats01 : Set (Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ))
  (hmats01 : mats01 = {A | ∀ i j : Fin (2 * n), A i j = 0 ∨ A i j = 1}) :
  (∑' A : mats01, (A.1 - (Matrix.transpose A)).det) / mats01.ncard = putnam_2016_b4_solution n :=
by
  have hm : ∀ M, M ∈ mats01 ↔ ∀ i j : Fin (2 * n), M i j = 0 ∨ M i j = 1 := by
    intro M; rw [hmats01]; rfl
  let e : (Fin (2*n) × Fin (2*n) → Bool) ≃ mats01 :=
    { toFun := fun f => ⟨Mf f, by
        rw [hm]; intro i j; simp only [Mf, vv]; split_ifs <;> simp⟩
      invFun := fun A p => decide (A.1 p.1 p.2 = 1)
      left_inv := by
        intro f; funext p; simp [Mf, vv]
      right_inv := by
        intro A; apply Subtype.ext; funext i j
        have := (hm A.1).mp A.2
        rcases this i j with h | h <;> simp [Mf, vv, h] }
  have hcard : (mats01.ncard : ℝ) = 2 ^ ((2*n) * (2*n)) := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr e]
    simp
  rw [← Equiv.tsum_eq e, tsum_fintype]
  have hs := sumdet n npos
  have hc := count_inv n npos
  have hc' : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (2*n)) => σ.cycleType = Multiset.replicate n 2)).card : ℝ)
      * (2 ^ n * (n.factorial : ℝ)) = ((2 * n).factorial : ℝ) := by exact_mod_cast hc
  have : ∑ f, ((e f).1 - (e f).1.transpose).det = ∑ f : Fin (2*n) × Fin (2*n) → Bool, (Mf f - (Mf f).transpose).det := rfl
  rw [this, hs, hcard]
  simp only [putnam_2016_b4_solution]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity), ← hc']
  have : (4:ℝ)^n = 2^n * 2^n := by rw [← mul_pow]; norm_num
  rw [this, one_div, inv_pow]
  field_simp
