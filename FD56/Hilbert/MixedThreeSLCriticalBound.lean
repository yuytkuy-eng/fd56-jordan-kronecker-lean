/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLCriticalBound

/-! Dimension lower bounds at degree six for mixed quotient three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_three_glHilbert_six (u v : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = 3*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) 6) =
      u*(u+3*v) := by
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2*Fintype.card m := by omega
  have hdiff : Fintype.card n-Fintype.card m = u+v := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) 3 u v hu hm hn
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hs := middle_gl_kernel_hilbert_shifted _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B) (mixedKernelDegree 3 u v)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    6 (by intro i; cases i <;> simp)
  have haux (d : ℕ) :
      Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree
          (genericAffineRows K n m * genericAffineSquare K n m *
            polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose d) =
        (Fintype.card m-(u+v))*(d+1)-(Fintype.card m+2*(u+v)) := by
    have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_middle_auxiliary_minimal_degrees B hmn hnm) d
    rw [balancedDegreeList_hilbert _ _ d (by omega), hdiff] at hh
    exact hh
  have h2 : (Fintype.card m-(u+v))*3-(Fintype.card m+2*(u+v)) = u+3*v := by omega
  have h1 : (Fintype.card m-(u+v))*2-(Fintype.card m+2*(u+v)) = 0 := by omega
  rw [hs]
  simp only [Fintype.sum_sum_type, mixedKernelDegree_inl, mixedKernelDegree_inr,
    Nat.reduceAdd, Nat.reduceSub, haux, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, h2,h1,mul_zero,add_zero]

theorem generic_mixed_three_slHilbert_six_lower (u v : ℕ) (hu : 0 < u)
    (hm : Fintype.card m = 3*(u+v)+v)
    (hn : Fintype.card n = Fintype.card m+(u+v)) (i₀ : n) :
    u*(u+3*v)+(8-u*v) ≤
      slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) 6 := by
  letI : Nonempty n := ⟨i₀⟩
  have hmn : Fintype.card m < Fintype.card n := by omega
  have hnm : Fintype.card n < 2*Fintype.card m := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) 3 u v hu hm hn
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hh := weighted_middle_slHilbert_lower _ _ B R hPR
    (mixedKernelDegree 3 u v) (Sum.elim (fun _ => 2) (fun _ => 1)) 6
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL
    (by intro i; cases i <;> simp) (by intro i; cases i <;> simp) (Sum.inl ⟨0,hu⟩)
  simp only [Fintype.sum_sum_type, mixedKernelDegree_inl, mixedKernelDegree_inr,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.reduceAdd] at hh
  have he :
      u*(Fintype.card m*3)+v*(Fintype.card m*2)+8+u*v =
        (u*(u*8+v*9)+v*(u*7+v*8))+u*(u+3*v)+8 := by rw [hm]; ring
  have hg := (generic_middle_slHilbert_bounds (K := K) i₀ hmn hnm 6).1
  rw [generic_mixed_three_glHilbert_six u v hu hm hn] at hg
  omega

end FD56
