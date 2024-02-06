import Mathlib

--statement of Siegel's Lemma, version 1 for the the integers
open Matrix
open BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

variable (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ )

--#check ‖A‖




--lemma box : Nat.card (Metric.ball (0 : Fin n → ℤ) x) = (2*x - 1)^n := by


variable (Lp Lm : Fin n → ℤ)

#check (Finset.Icc Lm Lp)

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


--Pigeonhole Finset.exists_ne_map_eq_of_card_lt_of_maps_to

--#check Σ j :Fin n , A (0 : Fin m) ( 0 : Fin

--variables (i : Fin m ) (j : Fin m)
--#check (∏  j : Fin n , (A i j))
-- maybe n = m + k  0 < k

-- i=1,..,m e j=1,.. ,n

theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) :
      ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖^(n-m) ≤ (n*‖A‖)^m    := by
   let B:= Nat.floor ((n*‖A‖)^(m/(n-m)))
   -- B' is the vector with all components = B'
   let B':= fun j : Fin n => (B: ℤ )
   -- T is the box [0 B]^n
   let T:= Finset.Icc 0 B'
   have hcardT : T.card=(B+1)^n := by
      simp
      rw [Pi.card_Icc 0 B']
      simp
   let P := fun i : Fin m =>( ∑  j : Fin n , B*( if 0 < (A i j) then A i j else 0))
   let N := fun i : Fin m =>( ∑  j : Fin n , B*( if (A i j) < 0 then -(A i j) else 0))
   let S:= Finset.Icc (-N) (P)
   let C:= Nat.floor ((‖A‖*n*B+1)^m)
   have hcardS : S.card = ∏ i : Fin m, (P i + N i + 1):= by sorry
   have hcardineq : S.card<T.card := by sorry
      -- zify
      -- rw [hcardT, hcardS]
      -- have haux : (C : ℝ)  < (B + 1) ^ n := by sorry
      -- norm_num  at haux
      -- norm_num
      -- norm_cast
      -- qify
   let f:= fun v : (Fin n → ℤ ) => A.mulVec v
   have him : ∀ v ∈  T, (f v) ∈  S := sorry
   rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardineq him with ⟨ x, hxT,y, hyT ,hneq, hfeq⟩
   use x+ -y
   -- proof that x - y ≠ 0
   refine ⟨sub_ne_zero.mpr hneq, ?_, ?_⟩
   simp at hfeq
   rw [← sub_eq_zero] at hfeq
   rw [A.mulVec_add, A.mulVec_neg]
   exact hfeq
   sorry




   --have him : ∀ v : Fin n → ℤ , ‖ A.mulVec v‖≤ (‖A‖ * n * B +1) := sorry


   --rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to
