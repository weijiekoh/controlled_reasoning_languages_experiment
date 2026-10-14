import Mathlib

abbrev Cards := Finset.Icc 1 100

abbrev Boxes := Fin 3

-- The trick is that given the sum of any two cards, the magician can tell a box number
abbrev Trick := ℕ → Boxes

-- The trick works when:
def trick_works (f : Cards → Boxes) (t : Trick) : Prop :=
  ∀ c₁ c₂ : Cards,
  -- given the sum of two cards from box 0 and box 1 then the trick gives the result of box 2 **and**
  (f c₁ = 0 → f c₂ = 1 → t (c₁.1 + c₂.1) = 2) ∧
  -- given the sum of two cards from box 0 and box 2 then the trick gives the result of box 1 **and**
  (f c₁ = 0 → f c₂ = 2 → t (c₁.1 + c₂.1) = 1) ∧
  -- given the sum of two cards from box 1 and box 2 then the trick gives the result of box 0
  (f c₁ = 1 → f c₂ = 2 → t (c₁.1 + c₂.1) = 0)

noncomputable abbrev imo_2000_p4_solution : ℕ := 12

/--
A magician has one hundred cards numbered $1$ to $100$. He puts them into three boxes, a red one, a white one and a blue one, so that each box contains at least one card. A member of the audience selects two of the three boxes, chooses one card from each and announces the sum of the numbers on the chosen cards. Given this sum, the magician identifies the box from which no card has been chosen. How many ways are there to put all the cards into the boxes so that this trick always works? (Two ways are considered different if at least one card is put into a different box.)
-/
theorem imo_2000_p4 (good_allocations : Finset (Cards → Boxes))
    (h : ∀ f, f ∈ good_allocations ↔ Function.Surjective f ∧ ∃ (t : Trick), trick_works f t) :
    good_allocations.card = imo_2000_p4_solution := by
  have classify : ∀ (F : ℕ → Fin 3),
      (∀ a b c d : ℕ, 1 ≤ a → a ≤ 100 → 1 ≤ b → b ≤ 100 → 1 ≤ c → c ≤ 100 → 1 ≤ d → d ≤ 100 → a + b = c + d → F a ≠ F b → F c ≠ F d → F a + F b = F c + F d) →
      (∀ x : Fin 3, ∃ n, 1 ≤ n ∧ n ≤ 100 ∧ F n = x) →
      (∃ σ : Equiv.Perm (Fin 3), ∀ n, 1 ≤ n → n ≤ 100 → F n = σ ⟨(n-1) % 3, by omega⟩) ∨
      (∃ σ : Equiv.Perm (Fin 3), ∀ n, 1 ≤ n → n ≤ 100 → F n = σ (if n = 1 then 0 else if n = 100 then 1 else 2)) := by
    intro F H hs
    have L1 : ∀ p q r x : Fin 3, p ≠ q → q ≠ r → p ≠ r → x ≠ p → x + p = q + r → False := by intro p q r x; revert p q r x; set_option synthInstance.maxSize 2000 in decide
    have L3 : ∀ p q r y : Fin 3, p ≠ q → r ≠ p → r ≠ q → y ≠ q → p + r = q + y → False := by decide
    have L4 : ∀ p q r z : Fin 3, p ≠ q → r ≠ p → r ≠ q → z ≠ p → p + z = q + r → False := by decide
    have L2 : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c → ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b ∧ σ 2 = c := by decide
    have L5 : ∀ p q : Fin 3, p ≠ q → -(p+q) ≠ p ∧ -(p+q) ≠ q := by decide
    obtain ⟨Rb, hRb⟩ : ∃ Rb : ℕ → Prop, ∀ i, Rb i ↔ (F i ≠ F (i+1) ∧ F (i+1) ≠ F (i+2) ∧ F i ≠ F (i+2)) := ⟨_, fun i => Iff.rfl⟩
    by_cases hr : ∃ k, 1 ≤ k ∧ k + 2 ≤ 100 ∧ Rb k
    · left
      obtain ⟨k, hk1, hk2, hk⟩ := hr
      have right : ∀ i, 1 ≤ i → i + 3 ≤ 100 → Rb i → F (i+3) = F i := by
        intro i h1 h2 h
        obtain ⟨a, b, c⟩ := (hRb i).1 h
        by_contra hne
        have := H (i+3) i (i+1) (i+2) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hne b
        exact L1 _ _ _ _ a b c hne this
      have left : ∀ i, 2 ≤ i → i + 2 ≤ 100 → Rb i → F (i-1) = F (i+2) := by
        intro i h1 h2 h
        obtain ⟨a, b, c⟩ := (hRb i).1 h
        by_contra hne
        have := H (i-1) (i+2) i (i+1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hne a
        -- x + r = p + q
        revert this hne a b c
        generalize F (i-1) = x
        generalize F i = p
        generalize F (i+1) = q
        generalize F (i+2) = r
        revert x p q r
        set_option synthInstance.maxSize 2000 in decide
      have rs : ∀ i, 1 ≤ i → i + 3 ≤ 100 → Rb i → Rb (i+1) := by
        intro i h1 h2 h
        have e := right i h1 h2 h
        obtain ⟨a, b, c⟩ := (hRb i).1 h
        rw [hRb]
        have e3 : i + 1 + 1 = i + 2 := rfl
        have e4 : i + 1 + 2 = i + 3 := rfl
        rw [e3, e4, e]
        exact ⟨b, fun h => c h.symm, fun h => a h.symm⟩
      have ls : ∀ i, 2 ≤ i → i + 2 ≤ 100 → Rb i → Rb (i-1) := by
        intro i h1 h2 h
        have e := left i h1 h2 h
        obtain ⟨a, b, c⟩ := (hRb i).1 h
        rw [hRb]
        have e3 : i - 1 + 1 = i := by omega
        have e4 : i - 1 + 2 = i + 1 := by omega
        rw [e3, e4, e]
        exact ⟨fun h => c h.symm, a, fun h => b h.symm⟩
      have up : ∀ d, k + d + 2 ≤ 100 → Rb (k + d) := by
        intro d
        induction d with
        | zero => intro _; simpa using hk
        | succ d ih =>
          intro h
          have := rs (k+d) (by omega) (by omega) (ih (by omega))
          simpa [Nat.add_assoc] using this
      have down : ∀ d, d + 1 ≤ k → Rb (k - d) := by
        intro d
        induction d with
        | zero => intro _; simpa using hk
        | succ d ih =>
          intro h
          have := ls (k-d) (by omega) (by omega) (ih (by omega))
          have e : k - d - 1 = k - (d+1) := by omega
          rw [e] at this
          exact this
      have allRb : ∀ i, 1 ≤ i → i + 2 ≤ 100 → Rb i := by
        intro i h1 h2
        by_cases hik : k ≤ i
        · have := up (i - k) (by omega)
          have e : k + (i - k) = i := by omega
          rwa [e] at this
        · have := down (k - i) (by omega)
          have e : k - (k - i) = i := by omega
          rwa [e] at this
      have per : ∀ n, 1 ≤ n → n + 3 ≤ 100 → F (n+3) = F n := fun n h1 h2 => right n h1 h2 (allRb n h1 (by omega))
      obtain ⟨a, b, c⟩ := (hRb 1).1 (allRb 1 (by omega) (by omega))
      obtain ⟨σ, s0, s1, s2⟩ := L2 (F 1) (F 2) (F 3) a b c
      refine ⟨σ, ?_⟩
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro h1 h2
        by_cases hn : n ≤ 3
        · interval_cases n
          · simpa using s0.symm
          · simpa using s1.symm
          · simpa using s2.symm
        · have := per (n-3) (by omega) (by omega)
          have e : n - 3 + 3 = n := by omega
          rw [e] at this
          rw [this, ih (n-3) (by omega) (by omega) (by omega)]
          congr 1
          apply Fin.ext
          simp [Fin.val_natCast]
          omega
    · right
      push_neg at hr
      have T : ∀ i j, 1 ≤ i → i + 1 ≤ 100 → 1 ≤ j → j ≤ 100 → F i ≠ F (i+1) → F j ≠ F i → F j ≠ F (i+1) →
          (j = 1 ∨ j = 100) ∧ (j = 100 → F 99 = F (i+1)) ∧ (j = 1 → F 2 = F i) := by
        intro i j hi1 hi2 hj1 hj2 hne hji hjq
        have hL : 2 ≤ j → F (j-1) = F (i+1) := by
          intro hj
          by_contra hn
          have := H i j (i+1) (j-1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hji.symm (fun h => hn h.symm)
          exact L3 _ _ _ _ hne hji hjq (fun h => hn h) this
        have hR : j ≤ 99 → F (j+1) = F i := by
          intro hj
          by_contra hn
          have := H i (j+1) (i+1) j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (fun h => hn h.symm) hjq.symm
          exact L4 _ _ _ _ hne hji hjq hn this
        refine ⟨?_, ?_, ?_⟩
        · by_contra hn
          push_neg at hn
          have e1 : j - 1 + 1 = j := by omega
          have e2 : j - 1 + 2 = j + 1 := by omega
          apply hr (j-1) (by omega) (by omega)
          rw [hRb, e1, e2, hL (by omega), hR (by omega)]
          exact ⟨hjq.symm, hji, fun h => hne h.symm⟩
        · rintro rfl
          simpa using hL (by omega)
        · rintro rfl
          simpa using hR (by omega)
      have trans : ∃ i, 1 ≤ i ∧ i + 1 ≤ 100 ∧ F i ≠ F (i+1) := by
        by_contra hn
        push_neg at hn
        have all : ∀ n, 1 ≤ n → n ≤ 100 → F n = F 1 := by
          intro n
          induction n with
          | zero => intro h; omega
          | succ m ih =>
            intro h1 h2
            by_cases hm : m = 0
            · subst hm; rfl
            · rw [← hn m (by omega) (by omega)]; exact ih (by omega) (by omega)
        obtain ⟨n, h1, h2, h3⟩ := hs (F 1 + 1)
        rw [all n h1 h2] at h3
        revert h3
        generalize F 1 = x
        revert x
        decide
      obtain ⟨i, hi1, hi2, hne⟩ := trans
      obtain ⟨j, hj1, hj2, hj⟩ := hs (-(F i + F (i+1)))
      obtain ⟨n1, n2⟩ := L5 _ _ hne
      have hji : F j ≠ F i := by rw [hj]; exact n1
      have hjq : F j ≠ F (i+1) := by rw [hj]; exact n2
      obtain ⟨T1, T2, T3⟩ := T i j hi1 hi2 hj1 hj2 hne hji hjq
      rcases T1 with rfl | rfl
      · -- j = 1
        have hF2 : F 2 = F i := T3 rfl
        have hA := T 1 (i+1) (by norm_num) (by norm_num) (by omega) hi2
          (by rw [show (1:ℕ)+1 = 2 from rfl, hF2]; exact hji) hjq.symm
          (by rw [show (1:ℕ)+1 = 2 from rfl, hF2]; exact hne.symm)
        obtain rfl : i = 99 := by omega
        have h100 : F 100 = F (99+1) := rfl
        have mid : ∀ n, 2 ≤ n → n ≤ 99 → F n = F 99 := by
          intro n hn1 hn2
          by_cases a : F n = F 99
          · exact a
          exfalso
          by_cases b : F n = F (99+1)
          · have := T 1 n (by norm_num) (by norm_num) (by omega) (by omega)
              (by rw [show (1:ℕ)+1 = 2 from rfl, hF2]; exact hji)
              (by rw [b]; exact hjq.symm) (by rw [show (1:ℕ)+1 = 2 from rfl, hF2]; exact a)
            omega
          · have := T 99 n (by norm_num) (by norm_num) (by omega) (by omega) hne a b
            omega
        obtain ⟨σ, s0, s1, s2⟩ := L2 (F 1) (F 100) (F 99) hjq (fun h => hne h.symm) hji
        refine ⟨σ, ?_⟩
        intro n h1 h2
        by_cases hn1 : n = 1
        · subst hn1; simpa using s0.symm
        by_cases hn2 : n = 100
        · subst hn2; simpa using s1.symm
        rw [if_neg hn1, if_neg hn2, s2, mid n (by omega) (by omega)]
      · -- j = 100
        have h99 : F 99 = F (i+1) := T2 rfl
        have h99' : F 99 ≠ F 100 := by rw [h99]; exact hjq.symm
        have hA := T 99 i (by norm_num) (by norm_num) hi1 (by omega) h99'
          (by rw [h99]; exact hne) hji.symm
        obtain rfl : i = 1 := by omega
        have mid : ∀ n, 2 ≤ n → n ≤ 99 → F n = F (1+1) := by
          intro n hn1 hn2
          by_cases a : F n = F 1
          · exfalso
            have := T 99 n (by norm_num) (by norm_num) (by omega) (by omega) h99'
              (by rw [h99, a]; exact hne) (by rw [a]; exact hji.symm)
            omega
          by_cases b : F n = F (1+1)
          · exact b
          · exfalso
            have := T 1 n (by norm_num) (by norm_num) (by omega) (by omega) hne a b
            omega
        obtain ⟨σ, s0, s1, s2⟩ := L2 (F 1) (F 100) (F (1+1)) hji.symm hjq (fun h => hne h)
        refine ⟨σ, ?_⟩
        intro n h1 h2
        by_cases hn1 : n = 1
        · subst hn1; simpa using s0.symm
        by_cases hn2 : n = 100
        · subst hn2; simpa using s1.symm
        rw [if_neg hn1, if_neg hn2, s2, mid n (by omega) (by omega)]
  let g1 : Cards → Boxes := fun c => ⟨(c.1 - 1) % 3, Nat.mod_lt _ (by norm_num)⟩
  let g2 : Cards → Boxes := fun c => if c.1 = 1 then 0 else if c.1 = 100 then 1 else 2
  have L7 : ∀ σ : Equiv.Perm (Fin 3), ∀ x y : Fin 3, x ≠ y → σ (-(x+y)) = -(σ x + σ y) := by decide
  have g1s : Function.Surjective g1 := by
    intro y
    fin_cases y
    · exact ⟨⟨1, by simp⟩, rfl⟩
    · exact ⟨⟨2, by simp⟩, rfl⟩
    · exact ⟨⟨3, by simp⟩, rfl⟩
  have g2s : Function.Surjective g2 := by
    intro y
    fin_cases y
    · exact ⟨⟨1, by simp⟩, by simp [g2]⟩
    · exact ⟨⟨100, by simp⟩, by simp [g2]⟩
    · exact ⟨⟨2, by simp⟩, by simp [g2]⟩
  have Tg1 : ∀ c1 c2 : Cards, g1 c1 ≠ g1 c2 → (fun s : ℕ => -(⟨(s-2) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)) (c1.1 + c2.1) = -(g1 c1 + g1 c2) := by
    intro c1 c2 _
    have a1 := (Finset.mem_Icc.1 c1.2)
    have a2 := (Finset.mem_Icc.1 c2.2)
    have e : (⟨(c1.1 + c2.1 - 2) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = g1 c1 + g1 c2 := by
      apply Fin.ext
      simp [g1, Fin.val_add]
      omega
    show -(⟨(c1.1 + c2.1 - 2) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = _
    rw [e]
  have Tg2 : ∀ c1 c2 : Cards, g2 c1 ≠ g2 c2 → (fun s : ℕ => if s ≤ 100 then (1:Fin 3) else if s = 101 then 2 else 0) (c1.1 + c2.1) = -(g2 c1 + g2 c2) := by
    intro c1 c2 hne
    have a1 := (Finset.mem_Icc.1 c1.2)
    have a2 := (Finset.mem_Icc.1 c2.2)
    simp only [g2] at hne ⊢
    split_ifs at hne ⊢ <;> first | omega | (exfalso; exact hne rfl) | decide
  have good : ∀ (g : Cards → Boxes) (t : ℕ → Fin 3), Function.Surjective g →
      (∀ c1 c2 : Cards, g c1 ≠ g c2 → t (c1.1 + c2.1) = -(g c1 + g c2)) →
      ∀ σ : Equiv.Perm (Fin 3), (⇑σ ∘ g) ∈ good_allocations := by
    intro g t hg hT σ
    rw [h]
    refine ⟨σ.surjective.comp hg, fun s => σ (t s), ?_⟩
    intro c1 c2
    have key : ∀ (x y : Fin 3), σ x = 0 → σ y = 1 → σ x ≠ σ y := by
      intro x y h1 h2; rw [h1, h2]; decide
    refine ⟨?_, ?_, ?_⟩
    · intro h1 h2
      have hne : g c1 ≠ g c2 := fun e => by
        simp only [Function.comp] at h1 h2; rw [e] at h1; rw [h1] at h2; exact absurd h2 (by decide)
      simp only [Function.comp] at h1 h2
      show σ (t (c1.1 + c2.1)) = _
      rw [hT c1 c2 hne, L7 σ _ _ hne, h1, h2]; decide
    · intro h1 h2
      have hne : g c1 ≠ g c2 := fun e => by
        simp only [Function.comp] at h1 h2; rw [e] at h1; rw [h1] at h2; exact absurd h2 (by decide)
      simp only [Function.comp] at h1 h2
      show σ (t (c1.1 + c2.1)) = _
      rw [hT c1 c2 hne, L7 σ _ _ hne, h1, h2]; decide
    · intro h1 h2
      have hne : g c1 ≠ g c2 := fun e => by
        simp only [Function.comp] at h1 h2; rw [e] at h1; rw [h1] at h2; exact absurd h2 (by decide)
      simp only [Function.comp] at h1 h2
      show σ (t (c1.1 + c2.1)) = _
      rw [hT c1 c2 hne, L7 σ _ _ hne, h1, h2]; decide
  have eq : good_allocations = (Finset.univ.image (fun σ : Equiv.Perm (Fin 3) => ⇑σ ∘ g1)) ∪ (Finset.univ.image (fun σ : Equiv.Perm (Fin 3) => ⇑σ ∘ g2)) := by
    ext f
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hf
      obtain ⟨hsurj, t, ht⟩ := (h f).1 hf
      obtain ⟨F, hF⟩ : ∃ F : ℕ → Fin 3, ∀ a (ha : 1 ≤ a ∧ a ≤ 100), F a = f ⟨a, Finset.mem_Icc.2 ha⟩ :=
        ⟨fun n => if hn : 1 ≤ n ∧ n ≤ 100 then f ⟨n, Finset.mem_Icc.2 hn⟩ else 0, fun a ha => by simp [ha]⟩
      have key : ∀ a b (ha : a ∈ Finset.Icc 1 100) (hb : b ∈ Finset.Icc 1 100), f ⟨a, ha⟩ ≠ f ⟨b, hb⟩ →
          t (a + b) = -(f ⟨a, ha⟩ + f ⟨b, hb⟩) := by
        intro a b ha hb hab
        have h1 := ht ⟨a, ha⟩ ⟨b, hb⟩
        have h2 := ht ⟨b, hb⟩ ⟨a, ha⟩
        simp only [Nat.add_comm b a] at h2
        simp only at h1 h2
        revert h1 h2 hab
        generalize f ⟨a, ha⟩ = p
        generalize f ⟨b, hb⟩ = q
        generalize t (a + b) = x
        revert p q x
        decide
      have H : ∀ a b c d : ℕ, 1 ≤ a → a ≤ 100 → 1 ≤ b → b ≤ 100 → 1 ≤ c → c ≤ 100 → 1 ≤ d → d ≤ 100 → a + b = c + d → F a ≠ F b → F c ≠ F d → F a + F b = F c + F d := by
        intro a b c d ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 hs hab hcd
        rw [hF a ⟨ha1, ha2⟩, hF b ⟨hb1, hb2⟩] at hab ⊢
        rw [hF c ⟨hc1, hc2⟩, hF d ⟨hd1, hd2⟩] at hcd ⊢
        have e1 := key a b (Finset.mem_Icc.2 ⟨ha1, ha2⟩) (Finset.mem_Icc.2 ⟨hb1, hb2⟩) hab
        have e2 := key c d (Finset.mem_Icc.2 ⟨hc1, hc2⟩) (Finset.mem_Icc.2 ⟨hd1, hd2⟩) hcd
        rw [hs, e2] at e1
        exact neg_injective e1.symm
      have hs : ∀ x : Fin 3, ∃ n, 1 ≤ n ∧ n ≤ 100 ∧ F n = x := by
        intro x
        obtain ⟨c, hc⟩ := hsurj x
        have hc2 := Finset.mem_Icc.1 c.2
        exact ⟨c.1, hc2.1, hc2.2, by rw [hF c.1 hc2]; exact hc⟩
      rcases classify F H hs with ⟨σ, hσ⟩ | ⟨σ, hσ⟩
      · left
        refine ⟨σ, ?_⟩
        funext c
        have hc2 := Finset.mem_Icc.1 c.2
        have := hσ c.1 hc2.1 hc2.2
        rw [hF c.1 hc2] at this
        exact this.symm
      · right
        refine ⟨σ, ?_⟩
        funext c
        have hc2 := Finset.mem_Icc.1 c.2
        have := hσ c.1 hc2.1 hc2.2
        rw [hF c.1 hc2] at this
        exact this.symm
    · rintro (⟨σ, rfl⟩ | ⟨σ, rfl⟩)
      · exact good g1 (fun s : ℕ => -(⟨(s-2) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)) g1s Tg1 σ
      · exact good g2 (fun s : ℕ => if s ≤ 100 then (1:Fin 3) else if s = 101 then 2 else 0) g2s Tg2 σ
  rw [eq, Finset.card_union_of_disjoint]
  · have inj : ∀ g : Cards → Boxes, Function.Surjective g → Function.Injective (fun σ : Equiv.Perm (Fin 3) => ⇑σ ∘ g) := by
      intro g hg a b hab
      apply Equiv.ext
      intro x
      obtain ⟨c, rfl⟩ := hg x
      exact congrFun hab c
    rw [Finset.card_image_of_injective _ (inj g1 g1s), Finset.card_image_of_injective _ (inj g2 g2s)]
    norm_num [Fintype.card_perm, Nat.factorial, imo_2000_p4_solution]
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro f ⟨σ, rfl⟩ ⟨τ, hτ⟩
    have e2 := congrFun hτ ⟨2, by simp⟩
    have e3 := congrFun hτ ⟨3, by simp⟩
    simp [g1, g2] at e2 e3
    exact absurd (σ.injective (e2.symm.trans e3)) (by decide)
