set -e
f=body.txt
# use perl for edits
perl -0pi -e 's/    simpa \[Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial\] using hP_symm/    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hP_symm/' $f
perl -0pi -e 's/    rw \[h2\] at h1\n    simp at h1\n    have h3 : Module.finrank ℝ \(LinearMap.ker Aᵀ.mulVecLin\) = 0/    rw [h2, Module.finrank_fin_fun] at h1\n    have h3 : Module.finrank ℝ (LinearMap.ker Aᵀ.mulVecLin) = 0/' $f
perl -0pi -e 's/intro h; apply hx; simpa using congrFun h \(Sum.inl : Fin n → _ \)/intro h; apply hx; funext i; simpa using congrFun h (Sum.inl i)/' $f
perl -0pi -e 's/simpa using congrFun hKv \(Sum.inl : Fin n → _\)/funext i; simpa using congrFun hKv (Sum.inl i)/' $f
perl -0pi -e 's/simpa using congrFun hKv \(Sum.inr : Fin p → _\)/funext i; simpa using congrFun hKv (Sum.inr i)/' $f
perl -0pi -e 's/rw \[← hA_rank\]; rfl/exact hA_rank/g' $f
perl -0pi -e 's/refine ⟨1, \?_, \?_, \?_⟩/refine ⟨(1 : Matrix (Fin p) (Fin p) ℝ), ?_, ?_, ?_⟩/; s/dotProduct x \(\(P \+ Aᵀ \* 1 \* A\)/dotProduct x ((P + Aᵀ * (1 : Matrix (Fin p) (Fin p) ℝ) * A)/' $f
perl -0pi -e 's/        have := h _ hA0 hFv\n        simpa \[[^\]]*\n[^\]]*\] using this/        have := h _ hA0 hFv\n        simp only [star_trivial]\n        rw [hFe]\n        exact this/' $f
perl -0pi -e 's/      rw \[← hv.\]\n      simpa \[[^\]]*\n[^\]]*\] using this/      have := hFe v\n      rw [hv'"'"'] at this\n      simp only [star_trivial] at *\n      rw [← this]\n      exact this2/' $f
