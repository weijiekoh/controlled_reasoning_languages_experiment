import Mathlib
example (s : Multiset ℂ) : ‖s.prod‖ = (s.map (‖·‖)).prod := by
  have := map_multiset_prod (normHom (α := ℂ)) s
  simpa using this
