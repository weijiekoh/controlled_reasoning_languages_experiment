import Mathlib

open Topology Filter Matrix

/--
Let $G$ be an abelian group with $n$ elements, and let $\{g_1=e,g_2,\dots,g_k\} \subsetneq G$ be a (not necessarily minimal) set of distinct generators of $G$. A special die, which randomly selects one of the elements $g_1,g_2,\dots,g_k$ with equal probability, is rolled $m$ times and the selected elements are multiplied to produce an element $g \in G$. Prove that there exists a real number $b \in (0,1)$ such that $\lim_{m \to \infty} \frac{1}{b^{2m}} \sum_{x \in G} (\text{Prob}(g=x)-\frac{1}{n})^2$ is positive and finite.
-/
theorem putnam_2011_a6
(G : Type*) [CommGroup G] [Fintype G]
(n : ℕ)
(gset : Set G)
(k : ℕ)
(mgprob : ℕ → G → ℝ)
(hmgprob : mgprob = (fun (m : ℕ) (x : G) => ({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℝ) / k ^ m))
(hn : n = (Fintype.elems : Finset G).card)
(hk : gset.encard = k)
(hgsetprop : k < n)
(hgset1 : 1 ∈ gset)
(hgsetgen : Subgroup.closure gset = ⊤)
: ∃ b ∈ Set.Ioo (0 : ℝ) 1, ∃ C > 0, Tendsto (fun m : ℕ => (1 / b ^ (2 * m)) * (∑ x : G, (mgprob m x - 1 / n) ^ 2)) atTop (𝓝 C) := by
  classical
  have hkc : gset.ncard = k := by
    rw [Set.ncard_def, hk]; simp
  have hkpos : 0 < k := by
    rw [← hkc]
    exact (Set.ncard_pos (Set.toFinite gset)).mpr ⟨1, hgset1⟩
  have hnG : n = Fintype.card G := by
    rw [hn]; rfl
  have hcA : Fintype.card (Additive G) = n := by rw [hnG]; exact (Fintype.card_congr Additive.ofMul).symm
  have hcardg : Fintype.card gset = k := by
    rw [← hkc, Set.ncard_eq_toFinset_card' gset, Set.toFinset_card]
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP : ∀ m x, mgprob m x = (({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℕ) : ℝ) / (k:ℝ)^m := by
    intro m x; rw [hmgprob]
  obtain ⟨zf, hzf⟩ : ∃ zf : AddChar (Additive G) ℂ → ℂ, ∀ ψ, zf ψ = (1 / (k:ℂ)) * ∑ s : gset, ψ (Additive.ofMul s.1) := ⟨_, fun _ => rfl⟩
  -- Fourier transform of the m-step distribution
  have hfour : ∀ (m : ℕ) (ψ : AddChar (Additive G) ℂ), ∑ x : G, ((mgprob m x : ℝ) : ℂ) * ψ (Additive.ofMul x) = zf ψ ^ m := by
    intro m ψ
    have hcount : ∀ x : G, ((mgprob m x : ℝ) : ℂ) = (1 / (k:ℂ)^m) * ∑ f : Fin m → gset, (if (∏ i : Fin m, (f i).1) = x then (1:ℂ) else 0) := by
      intro x
      have hc : (({f : Fin m → gset | (∏ i : Fin m, (f i).1) = x}.ncard : ℕ) : ℂ) = ∑ f : Fin m → gset, (if (∏ i : Fin m, (f i).1) = x then (1:ℂ) else 0) := by
        rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
        push_cast
        rfl
      rw [hP]
      push_cast
      rw [← hc]
      ring
    simp_rw [hcount]
    have h2 : ∑ x : G, (1 / (k:ℂ)^m * ∑ f : Fin m → gset, (if (∏ i : Fin m, (f i).1) = x then (1:ℂ) else 0)) * ψ (Additive.ofMul x)
        = 1 / (k:ℂ)^m * ∑ f : Fin m → gset, ψ (Additive.ofMul (∏ i : Fin m, (f i).1)) := by
      simp only [mul_assoc, Finset.mul_sum, Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_eq]
    rw [h2]
    have hsp : ∀ (s : Finset (Fin m)) (g : Fin m → Additive G), ψ (∑ i ∈ s, g i) = ∏ i ∈ s, ψ (g i) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    have h3 : ∀ f : Fin m → gset, ψ (Additive.ofMul (∏ i : Fin m, (f i).1)) = ∏ i : Fin m, ψ (Additive.ofMul (f i).1) := by
      intro f
      rw [← hsp]
      congr 1
    simp_rw [h3]
    have h4 : ∏ i : Fin m, ∑ s : gset, ψ (Additive.ofMul s.1) = ∑ f : Fin m → gset, ∏ i : Fin m, ψ (Additive.ofMul (f i).1) :=
      Fintype.prod_sum (fun _ (s : gset) => ψ (Additive.ofMul s.1))
    rw [hzf, mul_pow, _root_.one_div_pow, ← h4, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hz1 : zf 1 = 1 := by
    rw [hzf]
    simp [hcardg, hkpos.ne']
  have hsumP : ∀ m, ∑ x : G, mgprob m x = 1 := by
    intro m
    have h := hfour m 1
    simp only [AddChar.one_apply, mul_one, hz1, one_pow] at h
    exact_mod_cast h
  -- Parseval
  have horth : ∀ x y : G, ∑ ψ : AddChar (Additive G) ℂ, ψ (Additive.ofMul x) * ψ (-Additive.ofMul y) = if x = y then (n:ℂ) else 0 := by
    intro x y
    simp_rw [← AddChar.map_add_eq_mul]
    rw [AddChar.sum_apply_eq_ite, hcA]
    by_cases h : x = y
    · subst h; simp
    · have hne : Additive.ofMul x + -Additive.ofMul y ≠ 0 := by
        intro h'
        rw [add_neg_eq_zero] at h'
        exact h (Additive.ofMul.injective h')
      simp [hne, h]
  have hpars : ∀ m : ℕ, (n:ℂ) * ∑ x : G, ((mgprob m x : ℝ) : ℂ)^2 = ∑ ψ : AddChar (Additive G) ℂ, zf ψ ^ m * starRingEnd ℂ (zf ψ ^ m) := by
    intro m
    have hF : ∀ ψ : AddChar (Additive G) ℂ, starRingEnd ℂ (zf ψ ^ m) = ∑ y : G, ((mgprob m y : ℝ) : ℂ) * ψ (-Additive.ofMul y) := by
      intro ψ
      rw [← hfour m ψ, map_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [map_mul, Complex.conj_ofReal, ← AddChar.map_neg_eq_conj]
    have hterm : ∀ ψ : AddChar (Additive G) ℂ, zf ψ ^ m * starRingEnd ℂ (zf ψ ^ m) = ∑ x : G, ∑ y : G, ((mgprob m x : ℝ) : ℂ) * ((mgprob m y : ℝ) : ℂ) * (ψ (Additive.ofMul x) * ψ (-Additive.ofMul y)) := by
      intro ψ
      rw [hF ψ, ← hfour m ψ, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hsw : ∑ ψ : AddChar (Additive G) ℂ, ∑ x : G, ∑ y : G, ((mgprob m x : ℝ) : ℂ) * ((mgprob m y : ℝ) : ℂ) * (ψ (Additive.ofMul x) * ψ (-Additive.ofMul y))
        = ∑ x : G, ∑ y : G, ((mgprob m x : ℝ) : ℂ) * ((mgprob m y : ℝ) : ℂ) * (if x = y then (n:ℂ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, horth x y]
    have hrhs : ∑ x : G, ∑ y : G, ((mgprob m x : ℝ) : ℂ) * ((mgprob m y : ℝ) : ℂ) * (if x = y then (n:ℂ) else 0) = (n:ℂ) * ∑ x : G, ((mgprob m x : ℝ) : ℂ)^2 := by
      simp [mul_ite, sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [← hrhs, ← hsw]
    exact Finset.sum_congr rfl (fun ψ _ => (hterm ψ).symm)
  -- real form of Parseval
  have hterm2 : ∀ (m : ℕ) (ψ : AddChar (Additive G) ℂ), zf ψ ^ m * starRingEnd ℂ (zf ψ ^ m) = (((Complex.normSq (zf ψ)) ^ m : ℝ) : ℂ) := by
    intro m ψ
    rw [map_pow, ← mul_pow, Complex.mul_conj]
    push_cast
    ring
  have hreal : ∀ m : ℕ, ∑ x : G, (mgprob m x - 1 / (n:ℝ)) ^ 2 = (1 / (n:ℝ)) * ∑ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), (Complex.normSq (zf ψ)) ^ m := by
    intro m
    have h1 := hpars m
    rw [Finset.sum_congr rfl (fun ψ _ => hterm2 m ψ)] at h1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : AddChar (Additive G) ℂ))] at h1
    have hz1n : (Complex.normSq (zf 1)) ^ m = 1 := by rw [hz1]; simp
    rw [hz1n] at h1
    have h2 : (n:ℝ) * ∑ x : G, (mgprob m x)^2 = 1 + ∑ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), (Complex.normSq (zf ψ))^m := by
      exact_mod_cast h1
    have hexp : ∑ x : G, (mgprob m x - 1 / (n:ℝ))^2 = ∑ x : G, (mgprob m x)^2 - 2 * (1 / (n:ℝ)) * ∑ x : G, mgprob m x + n * (1 / (n:ℝ))^2 := by
      have hh : ∀ x : G, (mgprob m x - 1 / (n:ℝ))^2 = (mgprob m x)^2 - 2 * (1 / (n:ℝ)) * mgprob m x + (1 / (n:ℝ))^2 := fun x => by ring
      simp only [hh, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hnG]
    rw [hexp, hsumP m]
    have h3 : ∑ x : G, (mgprob m x)^2 = (1 + ∑ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), (Complex.normSq (zf ψ))^m) / n := by
      rw [eq_div_iff hnpos.ne', mul_comm]; exact h2
    rw [h3]
    field_simp
    ring
  -- a nontrivial character exists
  have hTne : (Finset.univ.erase (1 : AddChar (Additive G) ℂ)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : Fintype.card (AddChar (Additive G) ℂ) = n := by rw [AddChar.card_eq, hcA]
    omega
  obtain ⟨ψ0, hψ0T, hmax⟩ := Finset.exists_max_image (Finset.univ.erase (1 : AddChar (Additive G) ℂ)) (fun ψ => Complex.normSq (zf ψ)) hTne
  have hψ0ne : ψ0 ≠ 1 := (Finset.mem_erase.mp hψ0T).1
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ‖zf ψ0‖ := ⟨_, rfl⟩
  have hb2 : b^2 = Complex.normSq (zf ψ0) := by rw [hb, Complex.normSq_eq_norm_sq]
  have hbnn : 0 ≤ b := by rw [hb]; exact norm_nonneg _
  -- some x is not in gset
  have hx0 : ∃ x : G, x ∉ gset := by
    by_contra h
    push_neg at h
    have hu : gset = Set.univ := Set.eq_univ_of_forall h
    have : gset.ncard = n := by rw [hu, Set.ncard_univ, Nat.card_eq_fintype_card, hnG]
    omega
  obtain ⟨x0, hx0g⟩ := hx0
  have hP1x0 : mgprob 1 x0 = 0 := by
    rw [hP]
    have : {f : Fin 1 → gset | (∏ i : Fin 1, (f i).1) = x0} = ∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro f hf
      apply hx0g
      have h := hf
      simp only [Set.mem_setOf_eq, Fin.prod_univ_one] at h
      rw [← h]
      exact (f 0).2
    rw [this]; simp
  have hbpos : 0 < b := by
    rcases hbnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hq0 : Complex.normSq (zf ψ0) = 0 := by rw [← hb2, ← h]; ring
      have hzero : ∀ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), Complex.normSq (zf ψ) = 0 := by
        intro ψ hψ
        have h1 : Complex.normSq (zf ψ) ≤ Complex.normSq (zf ψ0) := hmax ψ hψ
        have h2 := Complex.normSq_nonneg (zf ψ)
        linarith
      have hsum0 : ∑ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), (Complex.normSq (zf ψ))^1 = 0 := by
        apply Finset.sum_eq_zero
        intro ψ hψ
        rw [hzero ψ hψ]; simp
      have hm1 := hreal 1
      rw [hsum0, mul_zero] at hm1
      have hterm : (mgprob 1 x0 - 1 / (n:ℝ))^2 ≤ ∑ x : G, (mgprob 1 x - 1 / (n:ℝ))^2 :=
        Finset.single_le_sum (f := fun x : G => (mgprob 1 x - 1 / (n:ℝ))^2) (fun x _ => sq_nonneg _) (Finset.mem_univ x0)
      rw [hm1, hP1x0] at hterm
      have h1n : (0:ℝ) < 1 / n := by positivity
      have hneg : (0:ℝ) - 1 / n = -(1 / n) := by ring
      rw [hneg, neg_sq] at hterm
      linarith [pow_pos h1n 2]
  -- every nontrivial character is nontrivial on gset
  have hle : ∀ ψ : AddChar (Additive G) ℂ, ‖zf ψ‖ ≤ 1 := by
    intro ψ
    rw [hzf, norm_mul]
    have hk' : ‖(1 / (k:ℂ))‖ = 1 / (k:ℝ) := by simp [norm_div]
    have hs : ‖∑ s : gset, ψ (Additive.ofMul s.1)‖ ≤ (k:ℝ) := by
      calc _ ≤ ∑ s : gset, ‖ψ (Additive.ofMul s.1)‖ := norm_sum_le _ _
        _ = (k:ℝ) := by simp [AddChar.norm_apply, hcardg]
    rw [hk']
    have hkr : (0:ℝ) < k := by exact_mod_cast hkpos
    calc 1 / (k:ℝ) * ‖∑ s : gset, ψ (Additive.ofMul s.1)‖ ≤ 1 / (k:ℝ) * k := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 1 := by field_simp
  have hgen : ∀ w : ℂ, ‖w‖ = 1 → w.re = 1 → w = 1 := by
    intro w hw hre
    have hsq : Complex.normSq w = 1 := by rw [Complex.normSq_eq_norm_sq, hw]; norm_num
    rw [Complex.normSq_apply, hre] at hsq
    have him : w.im = 0 := mul_self_eq_zero.mp (by linarith)
    exact Complex.ext (by simpa using hre) (by simpa using him)
  have hconst : ∀ ψ : AddChar (Additive G) ℂ, ‖zf ψ‖ = 1 → ∀ s ∈ gset, ψ (Additive.ofMul s) = zf ψ := by
    intro ψ hψ1
    have hzc : zf ψ * starRingEnd ℂ (zf ψ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ1]; simp
    have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
    have hsumz : ∑ s : gset, ψ (Additive.ofMul s.1) = (k:ℂ) * zf ψ := by
      rw [hzf]; field_simp
    have hwsum : ∑ s : gset, ψ (Additive.ofMul s.1) * starRingEnd ℂ (zf ψ) = k := by
      rw [← Finset.sum_mul, hsumz]
      calc (k:ℂ) * zf ψ * starRingEnd ℂ (zf ψ) = k * (zf ψ * starRingEnd ℂ (zf ψ)) := by ring
        _ = k := by rw [hzc, mul_one]
    have hwre : ∑ s : gset, (ψ (Additive.ofMul s.1) * starRingEnd ℂ (zf ψ)).re = k := by
      have := congrArg Complex.re hwsum
      rw [Complex.re_sum, Complex.natCast_re] at this
      exact this
    have hwle : ∀ s ∈ (Finset.univ : Finset gset), (ψ (Additive.ofMul s.1) * starRingEnd ℂ (zf ψ)).re ≤ 1 := by
      intro s _
      calc _ ≤ ‖ψ (Additive.ofMul s.1) * starRingEnd ℂ (zf ψ)‖ := Complex.re_le_norm _
        _ = 1 := by simp [norm_mul, AddChar.norm_apply, hψ1]
    have hdeq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun s : gset => (ψ (Additive.ofMul s.1) * starRingEnd ℂ (zf ψ)).re) (g := fun _ => 1) hwle).mp
      (by rw [hwre]; simp [hcardg])
    have hwone : ∀ s : gset, ψ (Additive.ofMul s.1) * starRingEnd ℂ (zf ψ) = 1 := by
      intro s
      apply hgen
      · simp [norm_mul, AddChar.norm_apply, hψ1]
      · exact hdeq s (Finset.mem_univ s)
    intro s hs
    have := hwone ⟨s, hs⟩
    calc ψ (Additive.ofMul s) = ψ (Additive.ofMul s) * (zf ψ * starRingEnd ℂ (zf ψ)) := by rw [hzc, mul_one]
      _ = (ψ (Additive.ofMul s) * starRingEnd ℂ (zf ψ)) * zf ψ := by ring
      _ = zf ψ := by rw [this, one_mul]
  have hconst1 : ∀ ψ : AddChar (Additive G) ℂ, ‖zf ψ‖ = 1 → ∀ s ∈ gset, ψ (Additive.ofMul s) = 1 := by
    intro ψ hψ1 s hs
    have h1 := hconst ψ hψ1 1 hgset1
    have h2 : ψ (Additive.ofMul (1:G)) = 1 := by simp
    rw [h2] at h1
    rw [hconst ψ hψ1 s hs, ← h1]
  have htriv : ∀ ψ : AddChar (Additive G) ℂ, (∀ s ∈ gset, ψ (Additive.ofMul s) = 1) → ψ = 1 := by
    intro ψ hψ
    let H : Subgroup G :=
      { carrier := {x | ψ (Additive.ofMul x) = 1}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at *
          rw [show Additive.ofMul (a*b) = Additive.ofMul a + Additive.ofMul b by simp, AddChar.map_add_eq_mul, ha, hb, one_mul]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a by simp, AddChar.map_neg_eq_conj, ha, map_one] }
    have hle2 : Subgroup.closure gset ≤ H := (Subgroup.closure_le H).mpr (fun s hs => hψ s hs)
    rw [hgsetgen] at hle2
    ext a
    have := hle2 (Subgroup.mem_top (Additive.toMul a))
    simp only [H, Subgroup.mem_mk, Set.mem_setOf_eq] at this
    simpa using this
  have hb1 : b < 1 := by
    by_contra hge
    push_neg at hge
    have hb1' : ‖zf ψ0‖ = 1 := by linarith [hle ψ0]
    exact hψ0ne (htriv ψ0 (fun s hs => hconst1 ψ0 hb1' s hs))
  -- limit
  have hL : ∀ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), Tendsto (fun m : ℕ => (Complex.normSq (zf ψ) / b^2)^m) atTop (𝓝 (if Complex.normSq (zf ψ) = b^2 then (1:ℝ) else 0)) := by
    intro ψ hψ
    have hle' : Complex.normSq (zf ψ) ≤ b^2 := by rw [hb2]; exact hmax ψ hψ
    have hnn : 0 ≤ Complex.normSq (zf ψ) / b^2 := div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)
    have hb2pos : 0 < b^2 := by positivity
    by_cases h : Complex.normSq (zf ψ) = b^2
    · rw [if_pos h]
      simp [h, div_self hb2pos.ne']
    · rw [if_neg h]
      have hlt : Complex.normSq (zf ψ) / b^2 < 1 := (div_lt_one hb2pos).mpr (lt_of_le_of_ne hle' h)
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt
  have hS := tendsto_finsetSum (Finset.univ.erase (1 : AddChar (Additive G) ℂ)) hL
  refine ⟨b, ⟨hbpos, hb1⟩, (1 / (n:ℝ)) * ∑ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), (if Complex.normSq (zf ψ) = b^2 then (1:ℝ) else 0), ?_, ?_⟩
  · have hpos1 : (1:ℝ) ≤ ∑ ψ ∈ Finset.univ.erase (1 : AddChar (Additive G) ℂ), (if Complex.normSq (zf ψ) = b^2 then (1:ℝ) else 0) := by
      have hsingle := Finset.single_le_sum (f := fun ψ => if Complex.normSq (zf ψ) = b^2 then (1:ℝ) else 0)
        (fun ψ _ => by split_ifs <;> norm_num) (Finset.mem_erase.mpr ⟨hψ0ne, Finset.mem_univ _⟩)
      have hif : (if Complex.normSq (zf ψ0) = b^2 then (1:ℝ) else 0) = 1 := by
        rw [if_pos hb2.symm]
      linarith
    exact mul_pos (by positivity) (by linarith)
  · refine Tendsto.congr (fun m => ?_) (hS.const_mul (1 / (n:ℝ)))
    have hd : ∀ ψ : AddChar (Additive G) ℂ, (Complex.normSq (zf ψ) / b^2)^m = Complex.normSq (zf ψ) ^ m / (b^2)^m := fun ψ => div_pow _ _ _
    simp only [hd]
    rw [hreal m, ← Finset.sum_div, pow_mul]
    ring
