  have hx : ∀ z : EuclideanSpace ℝ (Fin m),
      ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => f (x, z)) := fun z =>
    hf.comp (contDiff_id.prodMk contDiff_const)
  have hz : ∀ x : EuclideanSpace ℝ (Fin n),
      ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin m) => f (x, z)) := fun x =>
    hf.comp (contDiff_const.prodMk contDiff_id)
  constructor
  · rintro ⟨h1, h2⟩ p
    exact ⟨fun v => (convex_iff (hx p.2)).1 (h1 p.2) p.1 v,
      fun w => (concave_iff (hz p.1)).1 (h2 p.1) p.2 w⟩
  · intro H
    exact ⟨fun z => (convex_iff (hx z)).2 fun x v => (H (x, z)).1 v,
      fun x => (concave_iff (hz x)).2 fun z w => (H (x, z)).2 w⟩
