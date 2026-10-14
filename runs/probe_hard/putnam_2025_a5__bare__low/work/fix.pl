undef $/; $_=<STDIN>;
s/have := ih \(-a\); rw \[neg_neg\] at this; rw \[this\]/rw [neg_neg]; have := ih (-a); rw [neg_neg] at this; rw [this]/;
s/\(\(\{σ : Equiv.Perm \(Fin \(n \+ 1\)\) \|\n      ∀ i : Fin n, 0 < \(s i : ℤ\) \* \(\(σ i.succ : ℤ\) - \(σ i.castSucc : ℤ\)\)\}\).filter \(fun σ => σ 0 = y\)\).card/(Finset.filter (fun σ => σ 0 = y) (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>\n      ∀ i : Fin n, 0 < (s i : ℤ) * ((σ i.succ : ℤ) - (σ i.castSucc : ℤ))))).card/;
print;
