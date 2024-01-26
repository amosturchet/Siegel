import Mathlib

--statement of Siegel's Lemma, version 1 for the the integers
open Matrix

open BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ)

#check ‖A‖

-- maybe n = m + k  0 < k
theorem siegelsLemma  (hn: m < n) (hA : A ≠ 0 ) :
   ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖^(n-m) ≤ (n*‖A‖)^m    := by
  sorry



--lemma box : Nat.card (Metric.ball (0 : Fin n → ℤ) x) = (2*x - 1)^n := by


variable (Lp Lm : Fin n → ℤ)

#check (Finset.Icc Lm Lp).card

-- cardinality of integer points in a product of intervals
-- uses Icc

lemma aux1 (h : Lm ≤ Lp) : (Finset.Icc Lm Lp).card =
    ∏ i : Fin n, (Lp  i - Lm i + 1) := by
 rw [Pi.card_Icc Lm Lp, Nat.cast_prod]
 congr
 ext i
 rw [Int.card_Icc_of_le _ _ (by linarith [h i])]
 ring

--(Lp  i + Lm i + 1) := by
