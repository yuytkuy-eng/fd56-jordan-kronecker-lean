/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLCritical
import FD56.Hilbert.MixedSLHighDegree

/-! Low-degree vanishing and critical dimension bounds for mixed quotient two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slHilbert_zero_below (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (D d : ℕ) (hd : d ≤ D) (hzero : slHilbert M P D = 0) :
    slHilbert M P d = 0 := by
  rw [slHilbert_eq_matrix_kernel M P i₀ D] at hzero
  rw [slHilbert_eq_matrix_kernel M P i₀ d]
  obtain ⟨r,B,e,hB,hL,_,hH⟩ := polynomial_kernel_has_minimal_basis (slEquationMatrix M P i₀)
  rw [hH]
  apply Finset.sum_eq_zero
  intro i _
  have hh := Finset.single_le_sum (fun j _ => Nat.zero_le (D+1-e j)) (Finset.mem_univ i)
  rw [← hH D,hzero] at hh
  omega

theorem generic_mixed_two_slHilbert_low (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n)
    (d : ℕ) (hd : d ≤ 4) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d = 0 := by
  apply slHilbert_zero_below _ _ i₀ 4 d hd
  have hh := generic_mixed_slHilbert_critical_upper (K := K) 2 u v (by omega) hu hv hm hn i₀
  have hGL : Fintype.card m-4*(u+v) = 0 := by omega
  have ht : 2+4-3*(u+v)*v = 0 := by
    apply Nat.sub_eq_zero_of_le
    nlinarith
  simpa only [hGL,ht,mul_zero,add_zero,Nat.reduceAdd,Nat.le_zero] using hh

theorem generic_mixed_two_slHilbert_high_of_le (u v : ℕ) (hu : 0 < u) (huv : u ≤ v)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n)
    (d : ℕ) (hd : 6 ≤ d) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d)+(d+2) := by
  apply generic_mixed_slHilbert_of_row_dimension 2 u v (by omega) hu hm hn i₀ d (by omega)
  have hs : Fintype.card m-(u+v) = u+2*v := by omega
  have ht : 3 ≤ d-(2+2)+1 := by omega
  rw [hs]
  exact (show Fintype.card m+2*(u+v) ≤ (u+2*v)*3 by omega).trans
    (Nat.mul_le_mul_left _ ht)

theorem generic_mixed_glHilbert_shifted (a u v : ℕ) (ha : 2 ≤ a) (hu : 0 < u)
    (hm : Fintype.card m = a*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (d : ℕ) (hd : a+2 ≤ d) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      u*((Fintype.card m-(u+v))*(d-(a+1)+1)-(Fintype.card m+2*(u+v)))+
      v*((Fintype.card m-(u+v))*(d-(a+2)+1)-(Fintype.card m+2*(u+v))) := by
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2*Fintype.card m := by rw [hn,hm]; nlinarith
  have hdiff : Fintype.card n-Fintype.card m = u+v := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) a u v hu hm hn
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hs := middle_gl_kernel_hilbert_shifted _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B) (mixedKernelDegree a u v)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL d
    (by intro i; cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr] <;> omega)
  have haux (k : ℕ) :
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (genericAffineRows K n m * genericAffineSquare K n m *
            polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose k) =
        (Fintype.card m-(u+v))*(k+1)-(Fintype.card m+2*(u+v)) := by
    have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_middle_auxiliary_minimal_degrees B hmn hnm) k
    rw [balancedDegreeList_hilbert _ _ k (by omega),hdiff] at hh
    exact hh
  rw [hs]
  simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,haux,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.add_assoc,Nat.reduceAdd]

theorem generic_mixed_two_glHilbert_five (u v : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) 5) = u*(v-u) := by
  rw [generic_mixed_glHilbert_shifted 2 u v (by omega) hu hm hn 5 (by omega)]
  have h2 : (Fintype.card m-(u+v))*3-(Fintype.card m+2*(u+v)) = v-u := by omega
  have h1 : (Fintype.card m-(u+v))*2-(Fintype.card m+2*(u+v)) = 0 := by omega
  simp only [Nat.reduceAdd,Nat.reduceSub,h2,h1,mul_zero,add_zero]

theorem generic_mixed_two_glHilbert_six (u v : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) 6) =
      3*u*v+v*(v-u) := by
  rw [generic_mixed_glHilbert_shifted 2 u v (by omega) hu hm hn 6 (by omega)]
  have h3 : (Fintype.card m-(u+v))*4-(Fintype.card m+2*(u+v)) = 3*v := by omega
  have h2 : (Fintype.card m-(u+v))*3-(Fintype.card m+2*(u+v)) = v-u := by omega
  simp only [Nat.reduceAdd,Nat.reduceSub,h3,h2]
  ring

theorem generic_mixed_two_slHilbert_six_lower (u v : ℕ) (hu : 0 < u) (hvu : v ≤ u)
    (hm : Fintype.card m = 2*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    3*u*v+(8-v*(u-v)) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2*Fintype.card m := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) 2 u v hu hm hn
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hh := weighted_middle_slHilbert_lower _ _ B R hPR
    (mixedKernelDegree 2 u v) (Sum.elim (fun _ => 3) (fun _ => 2)) 6
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    (by intro i; cases i <;> simp) (by intro i; cases i <;> simp) (Sum.inl ⟨0,hu⟩)
  simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
    Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,Nat.reduceAdd] at hh
  have he : u*(Fintype.card m*4)+v*(Fintype.card m*3)+8 =
      (u*(u*8+v*9)+v*(u*7+v*8))+(2*u*v+v*v+8) := by rw [hm]; ring
  have hg := (generic_middle_slHilbert_bounds (K := K) i₀ hmn hnm 6).1
  rw [generic_mixed_two_glHilbert_six u v hu hm hn] at hg
  have ht : v-u = 0 := Nat.sub_eq_zero_of_le hvu
  rw [ht,mul_zero,add_zero] at hg
  have hs := Nat.sub_add_cancel hvu
  have hmul : v*(u-v)+v*v = u*v := by nlinarith
  have hthree : 3*u*v = 2*u*v+u*v := by ring
  rw [hthree] at hg ⊢
  omega

end FD56
