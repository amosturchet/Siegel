import Mathlib
set_option maxHeartbeats 1000000


--statement of Siegel's Lemma, version 1 for the the integers
open Matrix
open BigOperators
open Real
open Nat Set

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

lemma non_zero_mat_norm_ge_one ( hA : A ≠ 0 ) : 1 ≤ ‖A‖ := by
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



lemma norm_mat_int ( hA : A ≠ 0 )  : ∃ (a : ℕ ), ‖A‖=↑a ∧ 1 ≤  a := by
   --rw [<-sub_zero A,<-SeminormedAddGroup.dist_eq A 0]
   --rw [Matrix.norm_def,Pi.norm_def]
   --let x  := Finset.sup fun i =>( Finset.sup  (fun j => Int.natAbs (A i j)))
   --let i₀ : Fin m
   --let y:=Finset.sup Finset.univ fun b => ‖fun j => A b j‖₊
   have hexnnzentry : ∃  (i₀ : Fin m) (j₀ : Fin n), 1 ≤ Int.natAbs (A i₀ j₀) := by
      by_contra h
      push_neg at h
      apply hA
      convert_to ∀ (i₀ : Fin m) (j₀ : Fin n), A i₀ j₀ = 0
      exact Iff.symm ext_iff
      intro i₀ j₀
      specialize h i₀ j₀
      rw [<-Int.natAbs_eq_zero]
      exact lt_one_iff.mp h
   let maxr :=fun i =>( Finset.sup Finset.univ (fun j => Int.natAbs (A i j)))
   let x:= (Finset.sup Finset.univ fun i =>(maxr i ))
   have hone : 1 ≤ x := by
      rcases hexnnzentry with ⟨i₀,j₀,h₀ ⟩
      let f₁:= fun (k : Fin n) => Int.natAbs (A i₀ k)
      calc 1 ≤ Int.natAbs (A i₀ j₀) := by exact h₀
         _ = f₁ j₀ := by exact rfl
         _ ≤ maxr i₀ := by
            apply Finset.le_sup
            exact Finset.mem_univ j₀
         _ ≤ x := by
            apply Finset.le_sup
            exact Finset.mem_univ i₀
   use x
   constructor
   apply LE.le.antisymm
   rw [Matrix.norm_le_iff]
   intro i j
   rw [Int.norm_eq_abs]
   norm_cast
   rw [Int.abs_eq_natAbs]
   refine Int.ofNat_le.mpr ?h.a.a
   let f:= fun (k : Fin n) => Int.natAbs (A i k)
   calc Int.natAbs (A i j) = f j := by exact rfl
      _≤ maxr i := by
         apply Finset.le_sup
         exact Finset.mem_univ j
      _≤ x := by
         apply Finset.le_sup
         exact Finset.mem_univ i

   exact cast_nonneg x
   have extract_sup : ∃  (i₀ : Fin m) (j₀ : Fin n), x = Int.natAbs (A i₀ j₀) := by
      simp only
      sorry
   rcases extract_sup with ⟨i₀, j₀, h₀  ⟩
   rw [h₀]
   calc ↑(Int.natAbs (A i₀ j₀)) ≤ ‖A i₀ j₀‖ := by
         rw [Int.norm_eq_abs]
         rw [Nat.cast_natAbs]
      _  ≤ ‖A‖ := by exact norm_entry_le_entrywise_sup_norm A
   exact hone



/- lemma facile (x y B':  ℤ ) (hB'pos : 0 < B' ) : x ∈ Finset.Icc 0 B' → y ∈ Finset.Icc 0 B' → x-y  ∈  Finset.Icc (-B') B':= by
   sorry
 -/
/- lemma boxbox (x y B': Fin n → ℤ ) (hB'pos : 0 < B' ) : x ∈ Finset.Icc 0 B' → y ∈ Finset.Icc 0 B' → x-y  ∈  Finset.Icc (-B') B':= by
   sorry -/

--esperimento cambio goal

/- noncomputable def D  :=  Nat.floor ((n*‖A‖)^(m/(n-m)))

#check D

--def D' : Fin n → ℤ  := fun j : Fin n =>  (D : ℤ )


theorem siegelsLemma2  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) : ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ t ∈ Finset.Icc  (-(↑( Nat.floor((n*‖A‖)^(m/(n-m))) ) )) Nat.floor((n*‖A‖)^(m/(n-m)))   := by
   sorry -/

theorem siegelsLemma  (hn: m < n) (hm: 0 < m) (hA : A ≠ 0 ) : ∃ (t: Fin n → ℤ), t ≠ 0 ∧ A.mulVec t = 0 ∧ ‖t‖ ≤ ((n*‖A‖)^((m : ℝ )/(n-m))) := by
   --have hnPos : 0 < n := by linarith
   have hone_le_n_A : 1 ≤ ↑n * ‖A‖ := by
      calc 1 ≤ ‖A‖ := by
            exact non_zero_mat_norm_ge_one _ _ _ hA
         _ ≤ ↑n * ‖A‖ := by
            apply le_mul_of_one_le_left
            exact le_trans (zero_le_one) (non_zero_mat_norm_ge_one _ _ _ hA)
            norm_cast
            exact one_le_of_lt hn
   let e : ℝ := ↑m / (↑n - ↑m)
   have hePos : 0 < e := by
      apply div_pos
      norm_cast
      apply sub_pos_of_lt
      norm_cast
   have hineq1 : 1 ≤  (n*‖A‖)^e:= by
      apply one_le_rpow hone_le_n_A (le_of_lt hePos)
   let B:= Nat.floor ((n*‖A‖)^e)
   have hBpos : 0 < B := by
      rw [Nat.floor_pos]
      exact hineq1
   -- B' is the vector with all components = B'
   let B':= fun j : Fin n => (B: ℤ )
   -- T is the box [0 B]^n
   let T:= Finset.Icc 0 B'
   have hcardT : T.card=(B+1)^n := by
      --simp only
      rw [Pi.card_Icc 0 B']
      simp only [Pi.zero_apply, Int.card_Icc, sub_zero, Int.toNat_ofNat_add_one, Finset.prod_const,
        Finset.card_fin]
   -- let P := fun i : Fin m =>( ∑  j : Fin n , B*( if 0 < (A i j) then A i j else 0))
   -- let N := fun i : Fin m => B * ( ∑  j : Fin n , ( if (A i j) < 0 then (A i j) else 0)) --cambiato il segno di N
   let P := fun i : Fin m => B * ( ∑  j : Fin n , Int.toNat (A i j ) : ℤ   )
   let N := fun i : Fin m => B * ( ∑  j : Fin n , - Int.toNat ( - A i j ) : ℤ  ) --cambiato le definizioni di P ed N
   let S:= Finset.Icc (N) (P) -- S is the box where the image of T goes
   have hineq2 : ∀ j : Fin m, N j ≤ P j + 1 := by  --provare a semplificare questa
      intro j
      calc N j ≤ 0 := by
            apply mul_nonpos_iff_pos_imp_nonpos.2
            constructor
            ·  intro hB
               apply Finset.sum_nonpos
               intro i hi
               by_cases h1 : (A j i) < 0
               simp only [Left.neg_nonpos_iff, cast_nonneg]
               simp only [Left.neg_nonpos_iff, cast_nonneg]
            intro h
            exact_mod_cast (le_of_lt hBpos)
         _ ≤ P j := by
            apply mul_nonneg_iff_pos_imp_nonneg.2
            constructor
            ·  intro hB
               apply Finset.sum_nonneg
               intro i hi
               by_cases h1 : (A j i) < 0
               simp only [cast_nonneg]
               simp only [cast_nonneg]
            intro h
            exact_mod_cast (le_of_lt hBpos)
         _ ≤ P j + 1 := by exact Int.le_add_one (le_refl P j)
   have hcardS : S.card = (∏ i : Fin m,  (P i - N i + 1)):= by
      rw [Pi.card_Icc (N) (P), Nat.cast_prod]
      congr
      ext j
      rw [Int.card_Icc_of_le _ _ (hineq2 j)]
      ring
   --da qui iniziano i conti pesanti per dimostrare la disuguaglianza di caridalità

   have heq : ↑⌊↑n * ‖A‖ * ↑B⌋₊=↑⌊↑n * ‖A‖⌋₊ * ↑B:= by
     /-  rw [Matrix.norm_def]
      simp -/
      rcases norm_mat_int m n A with ⟨a, ha⟩
      rw [ha]
      norm_cast
      rw [Nat.floor_coe,Nat.floor_coe]

   let C:= Nat.floor ((n*‖A‖*B+1))
   have hineq3 : ∀ i : Fin m, (P i - N i + 1) ≤ Nat.floor ((n*‖A‖*B+1)) := by
      intro i
      have h1 : P i - N i + 1 = B * ((∑ j : Fin n, ↑(Int.toNat (A i j))) +  ∑ j : Fin n, ↑(Int.toNat (-A i j))) + 1 := by
         simp only [Finset.sum_neg_distrib, mul_neg, sub_neg_eq_add, add_left_inj]
         rw [<-mul_add]
      rw [Nat.floor_add_one, h1]
      rw [heq, mul_comm _ B,Nat.cast_add,Nat.cast_one,Nat.cast_mul]
      apply add_le_add_right
      apply mul_le_mul
      exact Int.le_refl ↑B

      /-
      --rw [<-Int.cast_lt] at hBpos
      --apply Int.mul_le_mul_left (Int.cast_lt.2 hBpos)
      have h : ↑⌊(↑n * ‖A‖) ^ (↑m / ( (n : ℝ) - ↑m))⌋₊ * (∑ j : Fin n, ↑(Int.toNat (A i j)) + ∑ x : Fin n, ↑(Int.toNat (-A i x))) = (B : ℤ) * (∑ j : Fin n, ↑(Int.toNat (A i j)) + ∑ x : Fin n, ↑(Int.toNat (-A i x))) := by
         simp
      push_cast
      apply mul_le_mul_left ↑⌊(↑n * ‖A‖) ^ (↑m / (↑n - ↑m))⌋₊
      rw [h]

      norm_cast -/
      --convert_to B * (∑ x : Fin n, Int.toNat (A i x) + ∑ x : Fin n, Int.toNat (-A i x)) ≤
  /- B * ⌊↑n * ‖A‖⌋₊
      simp -/




      sorry    --da FARE
   /- have hcomp2 : 1 ≤ ‖A‖ * ↑n := by
      calc 1 ≤ ‖A‖ := by
            exact non_zero_mat_norm_ge_one _ _ _ hA
         _ ≤ ‖A‖ * ↑n := by
            apply le_mul_of_one_le_right
            exact le_trans (zero_le_one) (non_zero_mat_norm_ge_one _ _ _ hA)
            norm_cast -/
   have hCpos : 0 < C := by
      rw [Nat.floor_pos]
      calc 1 ≤ ↑n  * ‖A‖ := by exact hone_le_n_A
         _ ≤ ↑n  * ‖A‖  * ↑B := by
            apply le_mul_of_one_le_right
            exact le_trans (zero_le_one) (hone_le_n_A)
            norm_cast
         _ ≤ ↑n * ‖A‖ * ↑B + 1 := by simp only [le_add_iff_nonneg_right, zero_le_one]
      /- calc 1 ≤ ‖A‖ * ↑n  := by sorry -- exact hcomp2
         _ ≤ ‖A‖ * ↑n * ↑B := by sorry
            /- apply le_mul_of_one_le_right
            exact le_trans (zero_le_one) (hcomp2)
            norm_cast -/
         _ ≤ ‖A‖ * ↑n * ↑B + 1 := by linarith -/
   have hcompexp : (e * (n - m) )= m := by
      apply div_mul_cancel
      apply sub_ne_zero_of_ne
      norm_cast
      linarith [hn]
   have hineq4 : (↑n * ‖A‖)^(m) < ↑(B + 1) ^ ((n ) - m) := by --Aggiustare
      convert_to (↑n  * ‖A‖ )^(m : ℝ ) < ↑(B + 1) ^ ((n : ℝ ) - m)
      rw [rpow_nat_cast (↑n  * ‖A‖) m]
      rw [<-rpow_nat_cast (↑(B + 1)) (n-m)]
      congr
      rw [Nat.cast_sub (le_of_lt hn)]
      calc (↑n  * ‖A‖ )^(m : ℝ ) = ((n*‖A‖)^(m/((n : ℝ)-m)))^ ((n : ℝ)-m) := by
            rw [<-rpow_mul _ (m / (n - m)) (n-m),hcompexp]
            exact le_trans (zero_le_one) (hone_le_n_A)
         _ < ↑(B + 1) ^ ((n : ℝ)-m) :=by
            apply Real.rpow_lt_rpow
            apply rpow_nonneg
            exact le_trans (zero_le_one) (hone_le_n_A)
            simp only [cast_add, cast_one]
            exact lt_floor_add_one ((↑n * ‖A‖) ^ (m / ( (n : ℝ ) - ↑m)))
            simp only [sub_pos, cast_lt]
            exact hn





   have hineq5  : ( ↑((Nat.floor (n*‖A‖*B + n*‖A‖))^m ) : ℝ ) < (↑((B + 1) ^ n)  ) := by --AGGIUSTARE
      have h1 : n*‖A‖*B  + n*‖A‖ = n*‖A‖* (B  + 1) := by linarith
      rw [h1]
      have h2 : (↑n * ‖A‖ * (↑B + 1) )^ m < (↑B + 1) ^ n := by
         calc (↑n * ‖A‖ * (↑B + 1) )^ m =(↑n * ‖A‖)^m * (↑B + 1) ^ m := by  rw [mul_pow]
            _ < (↑B + 1) ^ (n-m) * (↑B + 1) ^ m := by
               rw [mul_lt_mul_right]
               push_cast at hineq4
               exact hineq4
               norm_cast
               rw [pow_pos_iff]
               linarith
               exact hm
               --sorry
               /- push_cast at hcomp3
               exact hcomp3
               norm_cast
               rw [pow_pos_iff]
               linarith
               exact hm -/
            _ = (↑B + 1) ^ n := by
               rw [mul_comm, pow_mul_pow_sub]
               exact le_of_lt hn
      push_cast
      apply lt_of_lt_of_le' h2
      apply pow_le_pow_left
      simp only [cast_nonneg]
      apply Nat.floor_le
      calc 0 ≤ ↑n * ‖A‖  := by exact le_trans zero_le_one hone_le_n_A
         _ ≤ ↑n * ‖A‖ * ↑B := by
            apply le_mul_of_one_le_right
            exact le_trans (zero_le_one) (hone_le_n_A)
            norm_cast
         _ ≤ ↑n * ‖A‖ * (↑B + 1 ):= by linarith

   have hcardineq : S.card<T.card := by
      zify
      rw [hcardT, hcardS]
      calc (∏ i : Fin m, (P i - N i + 1)) ≤ (C)^m := by
            convert_to (∏ i : Fin m, (P i - N i + 1)) ≤ (∏ i : Fin m, C : ℤ)
            simp
            apply Finset.prod_le_prod
            intro i hi
            linarith [hineq2 i]
            intro i hi
            exact hineq3 i
         _  ≤ ↑(Nat.floor (n*‖A‖*B + n*‖A‖))^m := by
            apply pow_le_pow_left
            norm_cast
            exact (le_of_lt hCpos)
            norm_cast
            apply Nat.floor_le_floor
            simp
            exact hone_le_n_A
         _  < ↑((B + 1) ^ n) := by
            norm_cast
            exact Nat.cast_lt.1 (hineq5)
            --linarith [non_zero_mat_norm_ge_one _ _ _ hA, hnPos]
      -- zify
      -- rw [hcardT, hcardS]
      -- have haux : (C : ℝ)  < (B + 1) ^ n := by sorry
      -- norm_num  at haux
      -- norm_num
      -- norm_cast
      -- qify

   --fine conti

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
      simp only [Finset.sum_neg_distrib, mul_neg]
      rw [Finset.mul_sum,neg_eq_neg_one_mul,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      rw [neg_one_mul, neg_le]
      by_cases hsign : A i j ≤ 0
      ·  rw [ Int.toNat_of_nonneg, mul_comm]
         simp only [mul_neg, neg_le_neg_iff]
         apply mul_le_mul_of_nonpos_right
         exact hv.2 j
         exact hsign
         linarith
      ·  simp only [not_le] at hsign
         rw [Int.toNat_eq_zero.2]
         simp only [CharP.cast_eq_zero, mul_zero, Left.neg_nonpos_iff]
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
      simp only
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hsign : A i j ≤ 0
      ·  rw [Int.toNat_eq_zero.2]
         simp only [CharP.cast_eq_zero, mul_zero]
         apply mul_nonpos_of_nonpos_of_nonneg
         exact hsign
         exact hv.1 j
         exact hsign
      ·  simp only [not_le] at hsign
         rw [ Int.toNat_of_nonneg, mul_comm]
         rw [mul_le_mul_iff_of_pos_right]
         exact hv.2 j
         exact hsign
         linarith

   --Pronti per Pigeonhole
   rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcardineq him with ⟨ x, hxT,y, hyT ,hneq, hfeq⟩
   use x-y
   -- proof that x - y ≠ 0
   refine ⟨sub_ne_zero.mpr hneq, ?_, ?_⟩
   rw [← sub_eq_zero] at hfeq
   rw [sub_eq_add_neg,A.mulVec_add, A.mulVec_neg]
   exact hfeq
   ---disuguaglianza
   rw [<-Matrix.norm_col,norm_le_iff (le_trans zero_le_one hineq1)]
   intro i j
   rw [Finset.mem_Icc] at hyT
   rw [Finset.mem_Icc] at hxT
   simp only [col_apply, Pi.sub_apply, ge_iff_le]
   rw [Int.norm_eq_abs]
   push_cast
   rw [abs_le]
   constructor
   --calc  -(↑n * ‖A‖) ^ e ≤ ↑(x i) - ↑(y i) := by sorry
   calc -(↑n * ‖A‖) ^ e ≤ - B' i := by
         simp only [Int.cast_ofNat, neg_le_neg_iff]
         exact (Nat.floor_le (le_trans zero_le_one hineq1))
      _  ≤ - ↑(y i) := by
         norm_cast
         simp only [neg_le_neg_iff]
         exact hyT.2 i
      _  ≤ ↑(x i) - ↑(y i) := by
         simp only [neg_le_sub_iff_le_add, le_add_iff_nonneg_left, Int.cast_nonneg]
         exact hxT.1 i
   calc ↑(x i) - ↑(y i) ≤ ↑(B' i) := by
         norm_cast
         simp only [tsub_le_iff_right]
         rw [<-add_zero ((x i))]
         apply Int.add_le_add
         exact hxT.2 i
         exact hyT.1 i
      _  ≤  (↑n * ‖A‖) ^ e := by
         apply le_trans' (Nat.floor_le (le_trans zero_le_one hineq1))
         simp only [Int.cast_ofNat, le_refl]

   /- calc ↑(x i) - ↑(y i) ≤ ↑(x i) := by

         sorry

         simp
         exact hyT.1 i
      _  ≤ B' i := by sorry
      _  ≤  (↑n * ‖A‖) ^ e := by
         apply le_trans' (Nat.floor_le (le_trans zero_le_one hineq1))   --AGGIUSTARE
         rw [Nat.cast_le]
 -/


         --norm_cast
         --exact hxT.2 i



/-

   calc -(↑n * ‖A‖) ^ (↑m / (↑n - ↑m)) ≤ - B' i := by
         simp
         exact (Nat.floor_le (le_trans zero_le_one hPos))
      _  ≤ - ↑(y i) := by
         simp
         norm_cast
         exact hyT.2 i
      _  ≤ ↑(x i) - ↑(y i) := by
         simp
         exact hxT.1 i
   calc ↑(x i) - ↑(y i) ≤ ↑(x i) := by
         simp
         exact hyT.1 i
      _  ≤  (↑n * ‖A‖) ^ (↑m / (↑n - ↑m)) := by
         apply le_trans' (Nat.floor_le (le_trans zero_le_one hPos))
         norm_cast
         exact hxT.2 i

 -/


--prova

   -- have hcardineqR : (S.card : ℝ ) < ( T.card : ℝ ) := by
   --    rw [hcardT]
   --    sorry
   -- have hcardineq' : S.card<T.card := by
--    exact Nat.cast_lt.1 hcardineqR
