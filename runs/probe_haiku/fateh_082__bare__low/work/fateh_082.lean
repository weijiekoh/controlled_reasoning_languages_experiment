import Mathlib

/--
Let \( D \) be a unique factorization domain.
Prove that if every nonzero prime ideal of \( D \) is maximal, then \( D \) is a principal ideal domain.
-/
theorem isPrincipalIdealRing_of_isPrime_ne_bot_isMaximal {D : Type} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D] (h : ∀ P : Ideal D, [P.IsPrime] → P ≠ ⊥ → P.IsMaximal) : IsPrincipalIdealRing D := by
  -- Key lemma: every two-generated ideal is principal
  have key : ∀ x : D, ∀ y : D, ∃ g : D, ∀ z : D, z ∈ Ideal.span {x, y} ↔ g ∣ z := by
    intro x
    refine WellFounded.induction (C := fun x => ∀ y : D, ∃ g : D, ∀ z : D, z ∈ Ideal.span {x, y} ↔ g ∣ z)
      (wellFounded_dvdNotUnit (α := D)) x ?_
    intro x ih y
    by_cases hx0 : x = 0
    · subst hx0
      refine ⟨y, fun z => ?_⟩
      rw [Ideal.mem_span_pair]
      constructor
      · rintro ⟨a, b, rfl⟩
        exact ⟨b, by ring⟩
      · rintro ⟨c, rfl⟩
        exact ⟨0, c, by ring⟩
    by_cases hxu : IsUnit x
    · refine ⟨1, fun z => ?_⟩
      have htop : Ideal.span {x, y} = ⊤ := by
        rw [Ideal.eq_top_iff_one]
        obtain ⟨u, hu⟩ := hxu
        have h1 : (1 : D) = ((u⁻¹ : Dˣ) : D) * x := by
          rw [← hu]; simp
        rw [h1]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      rw [htop]
      simp
    obtain ⟨p, hpirr, hpx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
    obtain ⟨x', rfl⟩ := hpx
    have hp0 : p ≠ 0 := hpirr.ne_zero
    have hpprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp hpirr
    have hpmax : (Ideal.span {p}).IsMaximal := by
      haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp0).mpr hpprime
      exact h _ (by
        intro hbot
        apply hp0
        have : p ∈ Ideal.span {p} := Ideal.subset_span rfl
        rw [hbot] at this
        exact (Submodule.mem_bot D).mp this)
    have hx'ne : x' ≠ 0 := right_ne_zero_of_mul hx0
    have hrel : DvdNotUnit x' (p * x') := by
      exact ⟨hx'ne, p, hpirr.not_isUnit, by ring⟩
    by_cases hpy : p ∣ y
    · obtain ⟨y', rfl⟩ := hpy
      obtain ⟨g', hg'⟩ := ih x' hrel y'
      refine ⟨p * g', fun z => ?_⟩
      rw [Ideal.mem_span_pair]
      constructor
      · rintro ⟨c, d, rfl⟩
        have hmem : c * x' + d * y' ∈ Ideal.span {x', y'} :=
          Ideal.mem_span_pair.mpr ⟨c, d, rfl⟩
        obtain ⟨k, hk⟩ := (hg' _).mp hmem
        exact ⟨k, by linear_combination p * hk⟩
      · rintro ⟨k, rfl⟩
        obtain ⟨a, b, hab⟩ := (Ideal.mem_span_pair).mp ((hg' g').mpr dvd_rfl)
        exact ⟨k * a, k * b, by linear_combination (k * p) * hab⟩
    · obtain ⟨g', hg'⟩ := ih x' hrel y
      refine ⟨g', fun z => ?_⟩
      have hnot : y ∉ Ideal.span {p} := by
        rw [Ideal.mem_span_singleton]; exact hpy
      obtain ⟨v, i, hi, hvi⟩ := hpmax.exists_inv hnot
      obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hi
      rw [Ideal.mem_span_pair]
      constructor
      · rintro ⟨c, d, rfl⟩
        rw [← hg']
        exact Ideal.mem_span_pair.mpr ⟨c * p, d, by ring⟩
      · intro hz
        obtain ⟨a, b, hab⟩ := (Ideal.mem_span_pair).mp ((hg' z).mpr hz)
        exact ⟨a * u, a * v * x' + b, by linear_combination (a * x') * hvi + hab⟩
  -- Main argument
  constructor
  intro I
  by_cases hI : I = ⊥
  · subst hI
    exact Submodule.IsPrincipal.mk ⟨0, by simp⟩
  have hne : ∃ x, x ∈ I ∧ x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hI (eq_bot_iff.mpr (fun x hx => by
      rw [Submodule.mem_bot]
      exact hcon x hx))
  obtain ⟨d, ⟨hdI, hd0⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := D)).has_min
    {x | x ∈ I ∧ x ≠ 0} (by obtain ⟨x, hx⟩ := hne; exact ⟨x, hx⟩)
  have hdiv : ∀ z ∈ I, d ∣ z := by
    intro z hz
    obtain ⟨g, hg⟩ := key d z
    have hdg : d ∈ Ideal.span {d, z} := Ideal.subset_span (by simp)
    have hzg : z ∈ Ideal.span {d, z} := Ideal.subset_span (by simp)
    have hgg : g ∈ Ideal.span {d, z} := (hg g).mpr dvd_rfl
    have hgd : g ∣ d := (hg d).mp hdg
    have hgz : g ∣ z := (hg z).mp hzg
    obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp hgg
    have hgI : g ∈ I := by
      rw [← hce]
      exact I.add_mem (I.mul_mem_left c hdI) (I.mul_mem_left e hz)
    obtain ⟨k, hk⟩ := hgd
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hd0
      rw [hk, zero_mul]
    by_cases hku : IsUnit k
    · obtain ⟨u, rfl⟩ := hku
      have hgeq : g = d * ((u⁻¹ : Dˣ) : D) := by
        rw [hk, mul_assoc, Units.mul_inv, mul_one]
      have hdg' : d ∣ g := ⟨((u⁻¹ : Dˣ) : D), hgeq⟩
      exact dvd_trans hdg' hgz
    · exact absurd (hmin g ⟨hgI, hg0⟩) (fun hc => hc ⟨hg0, k, hku, hk⟩)
  refine Submodule.IsPrincipal.mk ⟨d, ?_⟩
  apply le_antisymm
  · intro z hz
    rw [Ideal.mem_span_singleton]
    exact hdiv z hz
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hdI)
