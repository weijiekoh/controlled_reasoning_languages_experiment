import Mathlib
abbrev Cards := Finset.Icc 1 100
abbrev Boxes := Fin 3
abbrev Trick := ℕ → Boxes
def trick_works (f : Cards → Boxes) (t : Trick) : Prop :=
  ∀ c₁ c₂ : Cards,
  (f c₁ = 0 → f c₂ = 1 → t (c₁.1 + c₂.1) = 2) ∧
  (f c₁ = 0 → f c₂ = 2 → t (c₁.1 + c₂.1) = 1) ∧
  (f c₁ = 1 → f c₂ = 2 → t (c₁.1 + c₂.1) = 0)
noncomputable abbrev imo_2000_p4_solution : ℕ := 12

theorem classify (F : ℕ → Fin 3)
  (H : ∀ a b c d : ℕ, 1 ≤ a → a ≤ 100 → 1 ≤ b → b ≤ 100 → 1 ≤ c → c ≤ 100 → 1 ≤ d → d ≤ 100 → a + b = c + d → F a ≠ F b → F c ≠ F d → F a + F b = F c + F d)
  (hs : ∀ x : Fin 3, ∃ n, 1 ≤ n ∧ n ≤ 100 ∧ F n = x) :
  (∃ σ : Equiv.Perm (Fin 3), ∀ n, 1 ≤ n → n ≤ 100 → F n = σ ⟨(n-1) % 3, by omega⟩) ∨
  (∃ σ : Equiv.Perm (Fin 3), ∀ n, 1 ≤ n → n ≤ 100 → F n = σ (if n = 1 then 0 else if n = 100 then 1 else 2)) := sorry

theorem imo_2000_p4 (good_allocations : Finset (Cards → Boxes))
    (h : ∀ f, f ∈ good_allocations ↔ Function.Surjective f ∧ ∃ (t : Trick), trick_works f t) :
    good_allocations.card = imo_2000_p4_solution := by
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
