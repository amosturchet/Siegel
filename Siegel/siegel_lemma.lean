import Mathlib

--statement of Siegel's Lemma, version 1 for the the integers
open Matrix
open BigOperators

--attribute [local instance] Matrix.linftyOpNormedAddCommGroup
--questa norma che ci aveva suggerito Riccardo non va bene perchè è
-- $|A|_\infty = \operatorname{sup}i (\sum_j |A{ij}|)$


--questa qui sotto è quella giusta
attribute [local instance] Matrix.seminormedAddCommGroup

variable (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin n → ℤ )  --(B : Matrix (Fin 1) (Fin 1) ℤ)

--#check ‖A‖
--#check ‖(B 0 0)‖

--lemma box : Nat.card (Metric.ball (0 : Fin n → ℤ) x) = (2*x - 1)^n := by

variable (Lp Lm : Fin n → ℤ)

--#check (Finset.Icc Lm Lp)

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
--Matrix.norm_entry_le_entrywise_sup_norm

lemma non_zero_mat_norm_ge_one (hA : A ≠ 0 ):1≤ ‖A‖ := by
   have hexnnzentry : ∃  (i₀ : Fin m) (j₀ : Fin n), 1 ≤ A i₀ j₀  ∨ A i₀ j₀ ≤ -1 := by
      by_contra h
      push_neg at h
      apply hA
      convert_to ∀ (i₀ : Fin m) (j₀ : Fin n), A i₀ j₀ = 0
      exact Iff.symm ext_iff
      intro i₀ j₀
      linarith [h i₀ j₀]
   have h : ∃  (i₀ : Fin m) (j₀ : Fin n ) , 1 ≤ ‖(A i₀ j₀)‖ := by
      rcases hexnnzentry with ⟨i₀ , j₀ , h ⟩
      use  i₀
      use  j₀
      rw [Int.norm_eq_abs,Int.cast_abs,le_abs]
      cases h with
      | inl h₁ =>
         left
         exact Int.cast_one_le_of_pos h₁
      | inr h₂ =>
         right
         rw [le_neg]
         apply Int.cast_le_neg_one_of_neg
         exact Int.le_sub_one_iff.mp h₂
   rcases h with ⟨ i₀, j₀, h1⟩
   calc 1 ≤ ‖(A i₀ j₀)‖ := by exact h1
      _ ≤ ‖A‖ := by exact norm_entry_le_entrywise_sup_norm A


lemma boxbox (x y B': Fin n → ℤ ) (hB'pos : 0 < B' ) : x ∈ Finset.Icc 0 B' → y ∈ Finset.Icc 0 B' → x-y  ∈  Finset.Icc (-B') B':= by
   sorry

--esperimento cambio goal

/- noncomputable def D : ℕ :=  Nat.floor ((n*‖A‖)^(m/(n-m)))

#check Nat.floor ((n*‖A‖)^(m/(n-m)))

def D' : Fin n → ℤ  := (D : ℤ )
 -/

/- theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) :
      ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ t ∈ Finset.Icc ( - ↑Nat.floor ((n*‖A‖)^(m/(n-m)))) Nat.floor ((n*‖A‖)^(m/(n-m)))  := by
-/
theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) : ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖ ≤ (n*‖A‖)^(m/(n-m)) := by
   let B:= Nat.floor ((n*‖A‖)^(m/(n-m)))
   have hBpos : 0 < B := by
      rw [Nat.floor_pos]
      apply one_le_pow_of_one_le
      apply one_le_mul_of_one_le_of_one_le _ (non_zero_mat_norm_ge_one _ _ _ hA)
      rw [Nat.one_le_cast]
      linarith
   -- B' is the vector with all components = B'
   let B':= fun j : Fin n => (B: ℤ )
   -- T is the box [0 B]^n
   let T:= Finset.Icc 0 B'
   have hcardT : T.card=(B+1)^n := by
      simp
      rw [Pi.card_Icc 0 B']
      simp
   -- let P := fun i : Fin m =>( ∑  j : Fin n , B*( if 0 < (A i j) then A i j else 0))
   -- let N := fun i : Fin m => B * ( ∑  j : Fin n , ( if (A i j) < 0 then (A i j) else 0)) --cambiato il segno di N
   let P := fun i : Fin m => B * ( ∑  j : Fin n , Int.toNat (A i j ) : ℤ   )
   let N := fun i : Fin m => B * ( ∑  j : Fin n , - Int.toNat ( - A i j ) : ℤ  ) --cambiato le definizioni di P ed N
   let S:= Finset.Icc (N) (P)
   have hineq : ∀ j : Fin m, N j ≤ P j + 1 := by  --provare a semplificare questa
      intro j
      calc N j ≤ 0 := by
            apply mul_nonpos_iff_pos_imp_nonpos.2
            constructor
            ·  intro hB
               apply Finset.sum_nonpos
               intro i hi
               by_cases h1 : (A j i) < 0
               simp
               simp
            intro h
            linarith
         _ ≤ P j := by
            apply mul_nonneg_iff_pos_imp_nonneg.2
            constructor
            ·  intro hB
               apply Finset.sum_nonneg
               intro i hi
               by_cases h1 : (A j i) < 0
               simp
               simp
            intro h
            linarith
         _ ≤ P j + 1 := by linarith
   have hcardS : S.card = (∏ i : Fin m,  (P i - N i + 1)):= by
      rw [Pi.card_Icc (N) (P), Nat.cast_prod]
      congr
      ext j
      rw [Int.card_Icc_of_le _ _ (by linarith [hineq j])]
      ring
   let C:= Nat.floor ((‖A‖*n*B+1))
   have hcomp : ∀ i : Fin m, (P i - N i + 1) ≤ C := by sorry
   have hcardineq : S.card<T.card := by
      zify
      rw [hcardT, hcardS]
      calc (∏ i : Fin m, (P i - N i + 1)) ≤ (C)^m := by
            convert_to (∏ i : Fin m, (P i - N i + 1)) ≤ (∏ i : Fin m, C : ℤ)
            simp
            apply Finset.prod_le_prod
            intro i hi
            linarith [hineq i]
            intro i hi
            exact hcomp i
         _ < ↑((B + 1) ^ n) := by sorry

      -- zify
      -- rw [hcardT, hcardS]
      -- have haux : (C : ℝ)  < (B + 1) ^ n := by sorry
      -- norm_num  at haux
      -- norm_num
      -- norm_cast
      -- qify
   have him : ∀ v ∈  T, (A.mulVec v) ∈  S := by  --provare a semplificare
      intro v hv
      rw [Finset.mem_Icc] at hv
      rw [Finset.mem_Icc]
      constructor
      -- prove N i ≤ (A v) i
      intro i
     /-  have hN : ∑ j : Fin n, -↑(Int.toNat (-A i j)) ≤ ∑ j : Fin n, A i j := by
         apply Finset.sum_le_sum
         intro j hj
         norm_cast
         rw [neg_le]
         exact Int.self_le_toNat (-A i j) -/
      unfold Matrix.mulVec
      unfold dotProduct
      simp
      rw [Finset.mul_sum,neg_eq_neg_one_mul,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [neg_one_mul, neg_le]
      by_cases hsign : A i j ≤ 0
      ·  rw [ Int.toNat_of_nonneg, mul_comm]
         simp
         apply mul_le_mul_of_nonpos_right
         exact hv.2 j
         exact hsign
         linarith
      ·  simp at hsign
         rw [Int.toNat_eq_zero.2]
         simp
         rw [mul_nonneg_iff_of_pos_left]
         exact hv.1 j
         exact hsign
         linarith
      -- prove (A v) i ≤ P i
      intro i
      /- have hP :  ∑ j : Fin n, A i j ≤ ∑ j : Fin n, ↑(Int.toNat (A i j)) := by
         apply Finset.sum_le_sum
         intro j hj
         exact Int.self_le_toNat (A i j) -/
      unfold Matrix.mulVec
      unfold dotProduct
      simp
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hsign : A i j ≤ 0
      ·  rw [Int.toNat_eq_zero.2]
         simp
         apply mul_nonpos_of_nonpos_of_nonneg
         exact hsign
         exact hv.1 j
         exact hsign
      ·  simp at hsign
         rw [ Int.toNat_of_nonneg, mul_comm]
         rw [mul_le_mul_iff_of_pos_right]
         exact hv.2 j
         exact hsign
         linarith
   rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardineq him with ⟨ x, hxT,y, hyT ,hneq, hfeq⟩
   use x-y
   -- proof that x - y ≠ 0
   refine ⟨sub_ne_zero.mpr hneq, ?_, ?_⟩
   --simp at hfeq
   rw [← sub_eq_zero] at hfeq
   rw [sub_eq_add_neg,A.mulVec_add, A.mulVec_neg]
   exact hfeq
   ---dusiguaglianza
   --rw [norm_le_iff]
  /-  rw [<-Matrix.norm_col,norm_le_iff]
   intro i j
   simp -/

   sorry




   --have him : ∀ v : Fin n → ℤ , ‖ A.mulVec v‖≤ (‖A‖ * n * B +1) := sorry


   --rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to
