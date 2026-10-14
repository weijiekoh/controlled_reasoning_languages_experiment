import Mathlib

open Matrix

lemma key_mul_self (p : ℕ) [Fact p.Prime] (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M * M = 0 ↔ M 1 1 = -M 0 0 ∧ M 0 0 ^ 2 + M 0 1 * M 1 0 = 0 := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    have hs : M 0 0 + M 1 1 = 0 := by
      by_contra hne
      have hb : M 0 1 = 0 := by
        rcases mul_eq_zero.mp (show M 0 1 * (M 0 0 + M 1 1) = 0 by linear_combination h01) with h | h
        · exact h
        · exact absurd h hne
      have hc : M 1 0 = 0 := by
        rcases mul_eq_zero.mp (show M 1 0 * (M 0 0 + M 1 1) = 0 by linear_combination h10) with h | h
        · exact h
        · exact absurd h hne
      have ha : M 0 0 = 0 := by
        apply mul_self_eq_zero.mp
        linear_combination h00 - M 0 1 * hc
      have hd : M 1 1 = 0 := by
        apply mul_self_eq_zero.mp
        linear_combination h11 - M 1 0 * hb
      exact hne (by rw [ha, hd, add_zero])
    refine ⟨by linear_combination hs, ?_⟩
    linear_combination h00
  · rintro ⟨h1, h2⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1] <;>
      first | linear_combination h2 | linear_combination -h2 | ring_nf

lemma pow_p_zero_iff (p : ℕ) [hp : Fact p.Prime] (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M ^ p = 0 ↔ M * M = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  constructor
  · intro h
    have hdet : M.det = 0 := by
      have := congrArg Matrix.det h
      rw [Matrix.det_pow, Matrix.det_zero] at this
      exact pow_eq_zero_iff (by omega) |>.mp this
    have hCH : M * M = M.trace • M := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] at hdet ⊢ <;>
        first | linear_combination -hdet | linear_combination hdet | ring
    have hk : ∀ n : ℕ, M ^ (n+2) = (M.trace ^ (n+1)) • M := by
      intro n
      induction n with
      | zero => simp [pow_two, hCH]
      | succ k ih =>
        rw [show k + 1 + 2 = (k+2) + 1 by ring, pow_succ, ih, smul_mul_assoc, hCH, smul_smul, ← pow_succ]
    have h2 : M ^ p = (M.trace ^ (p-2+1)) • M := by
      have := hk (p-2)
      rwa [show p-2+2 = p by omega] at this
    rw [h] at h2
    rcases smul_eq_zero.mp h2.symm with ht | hM
    · have htr : M.trace = 0 := (pow_eq_zero_iff (by omega)).mp ht
      rw [hCH, htr, zero_smul]
    · rw [hM, mul_zero]
  · intro h
    have e : M ^ p = M^(p-2) * (M*M) := by
      rw [← pow_two, ← pow_add]; congr 1; omega
    rw [e, h, mul_zero]

lemma fiber_sum (p : ℕ) [Fact p.Prime] (b : ZMod p) :
    ∑ a : ZMod p, ∑ c : ZMod p, (if a ^ 2 + b * c = 0 then 1 else 0 : ℕ) = p := by
  by_cases hb : b = 0
  · subst hb
    simp [sq]
  · have hi : ∀ a c : ZMod p, (a ^ 2 + b * c = 0 ↔ c = -(a ^ 2) / b) := by
      intro a c
      rw [eq_div_iff hb]
      constructor <;> intro h <;> linear_combination h
    have hinner : ∀ a : ZMod p, ∑ c : ZMod p, (if a ^ 2 + b * c = 0 then 1 else 0 : ℕ) = 1 := by
      intro a
      simp only [hi a]
      simp
    simp only [hinner]
    simp [ZMod.card]

lemma card_nilp (p : ℕ) [Fact p.Prime] :
    Nat.card {M : Matrix (Fin 2) (Fin 2) (ZMod p) // M * M = 0} = p ^ 2 := by
  have e : {M : Matrix (Fin 2) (Fin 2) (ZMod p) // M * M = 0} ≃
      {x : ZMod p × ZMod p × ZMod p // x.2.1 ^ 2 + x.1 * x.2.2 = 0} :=
    { toFun := fun M => ⟨(M.1 0 1, M.1 0 0, M.1 1 0), (key_mul_self p M.1).mp M.2 |>.2⟩
      invFun := fun x => ⟨Matrix.of ![![x.1.2.1, x.1.1], ![x.1.2.2, -x.1.2.1]], by
          rw [key_mul_self]
          exact ⟨by simp, by simpa using x.2⟩⟩
      left_inv := by
        intro M
        apply Subtype.ext
        have h := (key_mul_self p M.1).mp M.2
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h.1]
      right_inv := by
        intro x
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, fiber_sum]
  simp [ZMod.card, sq]

lemma card_order_p (p : ℕ) [Fact p.Prime] :
    Nat.card {g : GL (Fin 2) (ZMod p) // g ^ p = 1} = p ^ 2 := by
  have e : {g : GL (Fin 2) (ZMod p) // g ^ p = 1} ≃ {M : Matrix (Fin 2) (Fin 2) (ZMod p) // M * M = 0} :=
    { toFun := fun g => ⟨(g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1, by
        have hg : ((g.1 : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p = 1 := by
          have := congrArg Units.val g.2
          rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
        have h1 : (1 + ((g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1)) ^ p = 1 := by
          rw [show 1 + ((g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) = (g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) by simp]
          exact hg
        rw [add_pow_char_of_commute p (Commute.one_left _), one_pow] at h1
        have h2 : ((g.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ p = 0 := by simpa using h1
        exact (pow_p_zero_iff p _).mp h2⟩
      invFun := fun M =>
        ⟨Units.mk (1 + M.1) (1 - M.1)
          (by rw [show (1 + M.1) * (1 - M.1) = 1 - M.1 * M.1 by noncomm_ring, M.2, sub_zero])
          (by rw [show (1 - M.1) * (1 + M.1) = 1 - M.1 * M.1 by noncomm_ring, M.2, sub_zero]),
          by
            apply Units.ext
            rw [Units.val_pow_eq_pow_val, Units.val_one]
            show (1 + M.1) ^ p = 1
            rw [add_pow_char_of_commute p (Commute.one_left _), one_pow,
              (pow_p_zero_iff p _).mpr M.2, add_zero]⟩
      left_inv := by
        intro g
        apply Subtype.ext
        apply Units.ext
        simp
      right_inv := by
        intro M
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, card_nilp]

lemma card_GL2_factor (p : ℕ) [hp : Fact p.Prime] :
    (Nat.card (GL (Fin 2) (ZMod p))).factorization p = 1 := by
  have h2 := hp.out.two_le
  have hG : Nat.card (GL (Fin 2) (ZMod p)) = p * (((p ^ 2 - 1) * (p - 1))) := by
    rw [card_GL_field, Fin.prod_univ_two, ZMod.card]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have e1 : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, sq]
    rw [e1]
    ring_nf
  rw [hG]
  have hq1 : p ^ 2 - 1 ≠ 0 := by
    have : 1 < p ^ 2 := by nlinarith
    omega
  have hq2 : p - 1 ≠ 0 := by omega
  have hnd : ¬ p ∣ (p ^ 2 - 1) * (p - 1) := by
    intro h
    rcases (Nat.Prime.dvd_mul hp.out).mp h with h | h
    · have hp2' : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
      have hsub := Nat.dvd_sub hp2' h
      have hone : p ^ 2 - (p ^ 2 - 1) = 1 := by
        have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      rw [hone] at hsub
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp hsub)
    · have := Nat.le_of_dvd (by omega) h
      omega
  rw [Nat.factorization_mul (by omega) (mul_ne_zero hq1 hq2), Finsupp.add_apply,
    Nat.Prime.factorization_self hp.out]
  simp [Nat.factorization_eq_zero_of_not_dvd hnd]

lemma card_sylow_card (p : ℕ) [Fact p.Prime] (P : Sylow p (GL (Fin 2) (ZMod p))) :
    Nat.card ↥(P : Subgroup (GL (Fin 2) (ZMod p))) = p := by
  rw [Sylow.card_eq_multiplicity, card_GL2_factor, pow_one]

lemma pow_mem_sylow (p : ℕ) [Fact p.Prime] (P : Sylow p (GL (Fin 2) (ZMod p)))
    (g : GL (Fin 2) (ZMod p)) (hg : g ∈ (P : Subgroup (GL (Fin 2) (ZMod p)))) : g ^ p = 1 := by
  have h := pow_card_eq_one' (G := ↥(P : Subgroup (GL (Fin 2) (ZMod p)))) (x := ⟨g, hg⟩)
  rw [card_sylow_card p P] at h
  have := congrArg Subtype.val h
  simpa using this

lemma sylow_eq_zpowers (p : ℕ) [Fact p.Prime] (P : Sylow p (GL (Fin 2) (ZMod p)))
    (g : GL (Fin 2) (ZMod p)) (hg1 : g ≠ 1) (hgp : g ^ p = 1)
    (hgP : g ∈ (P : Subgroup (GL (Fin 2) (ZMod p)))) :
    (P : Subgroup (GL (Fin 2) (ZMod p))) = Subgroup.zpowers g := by
  have hle : Subgroup.zpowers g ≤ (P : Subgroup (GL (Fin 2) (ZMod p))) :=
    (Subgroup.zpowers_le).mpr hgP
  have hcard : Nat.card ↥(Subgroup.zpowers g) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hgp hg1]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_sylow_card p P, hcard]))).symm

lemma exists_unique_sylow_mem (p : ℕ) [Fact p.Prime] (g : GL (Fin 2) (ZMod p)) (hg1 : g ≠ 1)
    (hgp : g ^ p = 1) : ∃! P : Sylow p (GL (Fin 2) (ZMod p)), g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) := by
  have hpH : IsPGroup p ↥(Subgroup.zpowers g) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hgp hg1, pow_one]
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hpH
  have hgQ : g ∈ (Q : Subgroup (GL (Fin 2) (ZMod p))) := hQ (Subgroup.mem_zpowers g)
  refine ⟨Q, hgQ, fun R hR => ?_⟩
  apply Sylow.ext
  rw [sylow_eq_zpowers p R g hg1 hgp hR, sylow_eq_zpowers p Q g hg1 hgp hgQ]

open Classical in
lemma sylow_card_filter (p : ℕ) [Fact p.Prime] (P : Sylow p (GL (Fin 2) (ZMod p))) :
    (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
      g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) ∧ g ≠ 1)).card = p - 1 := by
  have h1 : (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
      g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))))).card = p := by
    have hc : Nat.card ↥(P : Subgroup (GL (Fin 2) (ZMod p))) =
        (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
          g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))))).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← hc]
    exact card_sylow_card p P
  have h2 : (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
      g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) ∧ g ≠ 1)) =
      (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
        g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))))).erase 1 := by
    ext g
    simp [Finset.mem_erase, and_comm]
  rw [h2, Finset.card_erase_of_mem (by simp), h1]

open Classical in
lemma main_count (p : ℕ) [Fact p.Prime] :
    Nat.card (Sylow p (GL (Fin 2) (ZMod p))) = p + 1 := by
  have : Fintype (Sylow p (GL (Fin 2) (ZMod p))) := Fintype.ofFinite _
  have hA : ∑ P : Sylow p (GL (Fin 2) (ZMod p)),
      (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
        g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) ∧ g ≠ 1)).card
      = Fintype.card (Sylow p (GL (Fin 2) (ZMod p))) * (p - 1) := by
    rw [Finset.sum_congr rfl (fun P _ => sylow_card_filter p P)]
    simp [Finset.sum_const, mul_comm]
  have hB : ∑ P : Sylow p (GL (Fin 2) (ZMod p)),
      (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) =>
        g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) ∧ g ≠ 1)).card
      = ∑ g : GL (Fin 2) (ZMod p),
        (Finset.univ.filter (fun P : Sylow p (GL (Fin 2) (ZMod p)) =>
          g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) ∧ g ≠ 1)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hC : ∀ g : GL (Fin 2) (ZMod p),
      (Finset.univ.filter (fun P : Sylow p (GL (Fin 2) (ZMod p)) =>
        g ∈ (P : Subgroup (GL (Fin 2) (ZMod p))) ∧ g ≠ 1)).card
      = if (g ≠ 1 ∧ g ^ p = 1) then 1 else 0 := by
    intro g
    by_cases hc : g ≠ 1 ∧ g ^ p = 1
    · rw [if_pos hc]
      obtain ⟨P0, hP0, hu⟩ := exists_unique_sylow_mem p g hc.1 hc.2
      rw [Finset.card_eq_one]
      refine ⟨P0, ?_⟩
      ext Q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hQ, _⟩
        exact hu Q hQ
      · rintro rfl
        exact ⟨hP0, hc.1⟩
    · rw [if_neg hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro Q - ⟨hQ, hg1⟩
      exact hc ⟨hg1, pow_mem_sylow p Q g hQ⟩
  have hD : (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) => g ≠ 1 ∧ g ^ p = 1))
      = (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) => g ^ p = 1)).erase 1 := by
    ext g
    simp [Finset.mem_erase, and_comm]
  have hE : (Finset.univ.filter (fun g : GL (Fin 2) (ZMod p) => g ^ p = 1)).card = p ^ 2 := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact card_order_p p
  have key : Fintype.card (Sylow p (GL (Fin 2) (ZMod p))) * (p - 1) = p ^ 2 - 1 := by
    rw [← hA, hB, Finset.sum_congr rfl (fun g _ => hC g), Finset.sum_boole, hD,
      Finset.card_erase_of_mem (by simp), hE]
    simp
  have hpp : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    have h1 : 1 ≤ p := by have := Fact.out (p := p.Prime); have := this.two_le; omega
    have h1' : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ h1
    zify [h1, h1']
    ring
  have hpos : 0 < p - 1 := by have := (Fact.out (p := p.Prime)).two_le; omega
  rw [Nat.card_eq_fintype_card]
  rw [hpp] at key
  exact Nat.eq_of_mul_eq_mul_right hpos key

/--
Prove that the number of Sylow $p$-subgroups of $\operatorname{GL}_2(\mathbb{F}_p)$ is $p + 1$.
-/
theorem card_sylow_gl_two_eq_add_one (p : ℕ) [Fact p.Prime] :
    Nat.card (Sylow p <| GL (Fin 2) (ZMod p)) = p + 1 := by
  exact main_count p
