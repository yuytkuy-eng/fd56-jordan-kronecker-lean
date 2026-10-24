/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedOneSLHilbert

/-! Every minimal-degree multiplicity in the remaining middle SL range. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def mixedOneSLProfile (u v d : ℕ) : ℕ :=
  max (u*(v*(d-1)-(3*u+4*v))+v*(v*(d-2)-(3*u+4*v)))
    (((u+v)*v+1)*d+2-(3*u^2+8*u*v+6*v^2))

theorem listHilbert_count_from_profile (xs : List ℕ) (H : ℕ → ℕ)
    (hH : ∀ d : ℕ, listHilbert xs d=(H d : ℤ)) (h0 : H 0=0) (k : ℕ) :
    (xs.count k : ℤ)=(H k : ℤ)-2*(H (k-1) : ℤ)+(H (k-2) : ℤ) := by
  have hh0 : listHilbert xs 0=(H 0 : ℤ) := by simpa using hH 0
  have hh1 : listHilbert xs 1=(H 1 : ℤ) := by simpa using hH 1
  have he := (listHilbert_second_difference xs k).symm
  cases k with
  | zero =>
    simp only [Nat.cast_zero,zero_sub] at he
    rw [listHilbert_negative xs (-1) (by omega),listHilbert_negative xs (-2) (by omega),
      hh0,h0] at he
    simpa [h0] using he
  | succ k =>
    cases k with
    | zero =>
      norm_num only [Nat.cast_one,sub_self,Int.reduceSub] at he
      rw [listHilbert_negative xs (-1) (by omega),hh0,hh1,h0] at he
      simpa [h0] using he
    | succ k =>
      have h1 : ((k+2 : ℕ) : ℤ)-1=((k+1 : ℕ) : ℤ) := by omega
      have h2 : ((k+2 : ℕ) : ℤ)-2=(k : ℤ) := by omega
      change (xs.count (k+2) : ℤ)=_ at he ⊢
      rw [h1,h2,hH,hH,hH] at he
      simpa only [Nat.add_sub_cancel,Nat.add_sub_cancel_right] using he

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_middle_slHilbert_of_twice_gt
    (hlo : 3*Fintype.card m<2*Fintype.card n)
    (hhi : Fintype.card n<2*Fintype.card m) (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d =
      mixedOneSLProfile (2*Fintype.card n-3*Fintype.card m)
        (2*Fintype.card m-Fintype.card n) d := by
  exact generic_mixed_one_slHilbert_closed _ _ d (by omega) (by omega)
    (by omega) (by omega) i₀

theorem generic_mixed_one_sl_minimal_multiplicities (u v : ℕ)
    (hu : 0<u) (hv : 0<v)
    (hm : Fintype.card m=u+2*v) (hn : Fintype.card n=2*u+3*v) (i₀ : n) :
    ∃ (r : ℕ) (B : Basis (Fin r) (AffineCoefficientField K (MatrixParameters n m))[X]
        (LinearMap.ker (Matrix.toLin' (slEquationMatrix (genericAffineSquare K n m)
          (genericAffineRows K n m) i₀)))) (e : Fin r → ℕ),
      (∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤e j) ∧
      Function.Injective (Matrix.mulVec (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (e j))) ∧
      ∀ k, ((List.ofFn e).count k : ℤ)=
        (mixedOneSLProfile u v k : ℤ)-2*(mixedOneSLProfile u v (k-1) : ℤ)+
          (mixedOneSLProfile u v (k-2) : ℤ) := by
  obtain ⟨r,B,e,hB,hL,_,hHil⟩ := polynomial_kernel_has_minimal_basis
    (slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
  have hh (d : ℕ) : listHilbert (List.ofFn e) d=(mixedOneSLProfile u v d : ℤ) := by
    rw [listHilbert_ofFn,← hHil d,← slHilbert_eq_matrix_kernel _ _ i₀ d]
    rw [generic_mixed_one_slHilbert_closed u v d hu hv hm hn i₀]
    rfl
  have h0 : mixedOneSLProfile u v 0=0 := by
    unfold mixedOneSLProfile
    rw [← generic_mixed_one_slHilbert_closed (K := K) u v 0 hu hv hm hn i₀]
    exact generic_mixed_one_slHilbert_low u v 0 hu hv (by omega) hm hn i₀
  exact ⟨r,B,e,hB,hL,listHilbert_count_from_profile _ _ hh h0⟩

end FD56
