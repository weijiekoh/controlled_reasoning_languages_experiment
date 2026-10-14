import Mathlib

noncomputable section

open scoped Topology
open scoped Matrix.Norms.L2Operator
open scoped RealInnerProductSpace
open scoped Gradient
open scoped Matrix
open Filter
open scoped BigOperators

namespace «CAM-Bench-177»

def TransactionCostFunction (D : Set ℝ) := {x // x ∈ D} → ℝ

def convexConjugate (f : ℝ → EReal) : ℝ → EReal :=
  fun y => sSup (Set.range fun x : ℝ => (y : EReal) * (x : EReal) - f x)

theorem convexConjugate_eq_maximum_offsetting_profit
    (N M : ℕ)
    (pSell qSell : Fin N → ℝ)
    (pBuy qBuy : Fin M → ℝ)
    (pMid y : ℝ)
    (hSellPricePos : ∀ i, 0 < pSell i)
    (hSellQtyPos : ∀ i, 0 < qSell i)
    (hBuyPricePos : ∀ i, 0 < pBuy i)
    (hBuyQtyPos : ∀ i, 0 < qBuy i)
    (hSellSorted : StrictMono pSell)
    (hBuySorted : StrictAnti pBuy)
    (pOther : ℝ)
    (hpOther : pOther = pMid + y) :
    let T : ℝ → EReal :=
      fun q =>
        if hq : q ∈ Set.Icc (-(∑ i : Fin M, qBuy i)) (∑ i : Fin N, qSell i) then
          if q = 0 then
            (0 : EReal)
          else if 0 < q then
            (((sInf
                {A : ℝ |
                  ∃ k : Fin N,
                    (∑ i : Fin N, if i.1 < k.1 then qSell i else 0) < q ∧
                    q ≤ (∑ i : Fin N, if i.1 ≤ k.1 then qSell i else 0) ∧
                    A =
                      (∑ i : Fin N, if i.1 < k.1 then pSell i * qSell i else 0) +
                        pSell k * (q - ∑ i : Fin N, if i.1 < k.1 then qSell i else 0)}) -
              pMid * q : ℝ) : EReal)
          else
            (((-pMid * q) -
                sInf
                  {A : ℝ |
                    ∃ k : Fin M,
                      (∑ i : Fin M, if i.1 < k.1 then qBuy i else 0) < -q ∧
                      -q ≤ (∑ i : Fin M, if i.1 ≤ k.1 then qBuy i else 0) ∧
                      A =
                        (∑ i : Fin M, if i.1 < k.1 then pBuy i * qBuy i else 0) +
                          pBuy k * (-q - ∑ i : Fin M, if i.1 < k.1 then qBuy i else 0)} :
              ℝ) : EReal)
        else
          ⊤;
    convexConjugate T y =
      sSup
        {z : EReal |
          ∃ q : ℝ,
            q ∈ Set.Icc (-(∑ i : Fin M, qBuy i)) (∑ i : Fin N, qSell i) ∧
            z = (y : EReal) * (q : EReal) - T q} := by
  intro T
  unfold convexConjugate
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ Set.Icc (-(∑ i : Fin M, qBuy i)) (∑ i : Fin N, qSell i)
    · exact le_sSup ⟨x, hx, rfl⟩
    · have hT : T x = ⊤ := by
        simp only [T]
        rw [dif_neg hx]
      show (y : EReal) * (x : EReal) - T x ≤ _
      rw [hT]
      simp
  · apply sSup_le_sSup
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨q, rfl⟩

end «CAM-Bench-177»
