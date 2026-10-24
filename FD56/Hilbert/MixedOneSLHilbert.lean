/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneHankelArithmetic
import FD56.Hilbert.MixedOneLowerEnvelope
import FD56.Hilbert.MixedTwoSLCriticalBound

/-! The complete quotient-one SL Hilbert function in degrees at least three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_mixed_one_glHilbert_of_balanced (u v d : ℕ)
    (hu : 0<u) (hv : 0<v) (hd : 3≤d)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v)
    (h : Fin v → ℕ) (hb : (List.ofFn h).Perm (balancedDegreeList (3*u+4*v) v)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m)) d) =
      ∑ i : Fin u ⊕ Fin v, ∑ j, (d-(mixedKernelDegree 1 u v i+1)+1-h j) := by
  have hmn : Fintype.card m<Fintype.card n := by omega
  have hnm : Fintype.card n<2*Fintype.card m := by omega
  obtain ⟨B,hB,hBL⟩ := generic_mixed_kernel_basis (K := K) (n := n) (m := m)
    1 u v hu (by omega) (by omega)
  obtain ⟨R,_,hPR⟩ := generic_affine_rows_right_inverse_of_sizes K m n (by omega) hmn
  have hPL := matrix_transpose_injective_of_surjective _
    (generic_affine_rows_leading_surjective K m n hmn.le)
  have hs := middle_gl_kernel_hilbert_shifted _ _ B R hPR
    (generic_middle_kernel_transfer_injective hnm.le B) (mixedKernelDegree 1 u v)
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hB hBL hPL d
    (by intro i; cases i <;> simp only [mixedKernelDegree_inl,mixedKernelDegree_inr] <;> omega)
  have haux (k : ℕ) : Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (genericAffineRows K n m * genericAffineSquare K n m *
        polynomialKernelBasisMatrix (genericAffineRows K n m) B).transpose k)=∑ j, (k+1-h j) := by
    have he := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_middle_auxiliary_minimal_degrees B hmn hnm) k
    have hr : Fintype.card n-Fintype.card m=u+v := by omega
    have ht : Fintype.card m-(u+v)=v := by omega
    have hz : Fintype.card m+2*(u+v)=3*u+4*v := by omega
    rw [hr,ht,hz] at he
    have hb' := (hb.map (fun z => k+1-z)).sum_eq
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] at hb'
    exact he.trans hb'.symm
  rw [hs]
  simp_rw [haux]

set_option maxHeartbeats 800000 in
theorem generic_mixed_one_slHilbert_lower_envelope_eq (u v d : ℕ)
    (hu : 0<u) (hv : 0<v) (hd : 3≤d)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      max (Module.finrank (AffineCoefficientField K (MatrixParameters n m))
        (polynomialKernelAtDegree (glEquationMatrix (genericAffineSquare K n m)
          (genericAffineRows K n m)) d))
        (((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2)) := by
  apply Nat.le_antisymm _ (generic_mixed_one_slHilbert_lower_envelope u v d hu hv hd hm hn i₀)
  obtain ⟨h,hh,hs,hb⟩ := exists_positive_balanced_hankel_degrees u v hv
  obtain ⟨M,P,hM,hP,hbound⟩ := exists_mixed_one_hankel_upper_witness (n := n) (m := m)
    K u v d hv hd hm hn h hh hs
  have hupp := (generic_slHilbert_le_field_witness
    (algebraMap K (HankelCoefficientField K v (u+v))) M P hM hP i₀ d).trans hbound
  rw [mixedOneHankel_count_identity u v d h hd hs,
    ← generic_mixed_one_glHilbert_of_balanced (K := K) u v d hu hv hd hm hn h hb] at hupp
  exact hupp

theorem generic_mixed_one_glHilbert_closed (u v d : ℕ)
    (hu : 0<u) (hv : 0<v) (hd : 3≤d)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m)) d) =
      u*(v*(d-1)-(3*u+4*v))+v*(v*(d-2)-(3*u+4*v)) := by
  obtain ⟨h,_,_,hb⟩ := exists_positive_balanced_hankel_degrees u v hv
  rw [generic_mixed_one_glHilbert_of_balanced u v d hu hv hd hm hn h hb]
  have he (k : ℕ) : (∑ j, (k+1-h j))=v*(k+1)-(3*u+4*v) := by
    have ht := (hb.map (fun z => k+1-z)).sum_eq
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply,
      balancedDegreeList_hilbert _ _ k hv] using ht
  simp_rw [he]
  simp only [Fintype.sum_sum_type,mixedKernelDegree_inl,mixedKernelDegree_inr,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  rw [show d-(1+1)+1=d-1 by omega,show d-(1+1+1)+1=d-2 by omega]

theorem generic_mixed_one_slHilbert_closed_high (u v d : ℕ)
    (hu : 0<u) (hv : 0<v) (hd : 3≤d)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      max (u*(v*(d-1)-(3*u+4*v))+v*(v*(d-2)-(3*u+4*v)))
        (((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2)) := by
  rw [generic_mixed_one_slHilbert_lower_envelope_eq u v d hu hv hd hm hn i₀,
    generic_mixed_one_glHilbert_closed u v d hu hv hd hm hn]

theorem generic_mixed_one_slHilbert_low (u v d : ℕ)
    (hu : 0<u) (hv : 0<v) (hd : d≤3)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d=0 := by
  apply slHilbert_zero_below _ _ i₀ 3 d hd
  rw [generic_mixed_one_slHilbert_closed_high u v 3 hu hv (by omega) hm hn i₀]
  have h1 : v*(3-1)≤3*u+4*v := by omega
  have h2 : v*(3-2)≤3*u+4*v := by omega
  have h3 : ((u+v)*v+1)*3+2≤3*u^2+8*u*v+6*v^2 := by nlinarith
  rw [Nat.sub_eq_zero_of_le h1,Nat.sub_eq_zero_of_le h2,Nat.sub_eq_zero_of_le h3]
  simp

theorem generic_mixed_one_slHilbert_closed (u v d : ℕ)
    (hu : 0<u) (hv : 0<v)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) (i₀ : n) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      max (u*(v*(d-1)-(3*u+4*v))+v*(v*(d-2)-(3*u+4*v)))
        (((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2)) := by
  by_cases hd : 3≤d
  · exact generic_mixed_one_slHilbert_closed_high u v d hu hv hd hm hn i₀
  · rw [generic_mixed_one_slHilbert_low u v d hu hv (by omega) hm hn i₀]
    have h1 : v*(d-1)≤3*u+4*v := by nlinarith [Nat.sub_le d 1]
    have h2 : v*(d-2)≤3*u+4*v := by nlinarith [Nat.sub_le d 2]
    have h3 : ((u+v)*v+1)*3+2≤3*u^2+8*u*v+6*v^2 := by nlinarith
    have h4 : ((u+v)*v+1)*d+2≤3*u^2+8*u*v+6*v^2 :=
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega : d≤3)) 2).trans h3
    simp [Nat.sub_eq_zero_of_le h1,Nat.sub_eq_zero_of_le h2,Nat.sub_eq_zero_of_le h4]

end FD56
