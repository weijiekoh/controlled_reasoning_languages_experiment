perl -0pi -e 's/have : \(p \+\+ r\)\.length = \(p \+\+ r\x27\)\.length := by simp \[hl\]\n    rw \[← this\]/have this : (p ++ r\x27).length = (p ++ r).length := by simp [hl]\n    rw [this]/g' b.lean
