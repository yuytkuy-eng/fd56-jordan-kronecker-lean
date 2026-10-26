/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile
import FD56.LinearAlgebra.MixedKernelPairings

/-! Actual skew-pencil minimal degrees satisfy the Kronecker dimension bound. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem coefficient_pairing_dimension_bound {K n a b : Type*} [Field K]
    [Fintype n] [Fintype a] [Fintype b]
    [DecidableEq n] [DecidableEq a] [DecidableEq b]
    (W : Matrix n a K) (L : Matrix b n K)
    (hW : Function.Injective W.mulVec) (hL : Function.Surjective L.mulVec)
    (hLW : L*W=0) : Fintype.card a+Fintype.card b ≤ Fintype.card n := by
  have hrange : LinearMap.range (Matrix.toLin' W) ≤ LinearMap.ker (Matrix.toLin' L) := by
    rintro _ ⟨v,rfl⟩
    change L *ᵥ (W *ᵥ v)=0
    rw [Matrix.mulVec_mulVec,hLW,Matrix.zero_mulVec]
  have hr := LinearMap.finrank_range_of_inj (f := Matrix.toLin' W) hW
  have hk := Submodule.finrank_mono hrange
  rw [hr,Module.finrank_fintype_fun_eq_card] at hk
  have hd := (Matrix.toLin' L).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hL,finrank_top,
    Module.finrank_fintype_fun_eq_card,Module.finrank_fintype_fun_eq_card] at hd
  omega

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem skew_pencil_minimal_degrees_dimension_bound (A B : Matrix n n K)
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) xs)
    (hA : A.transpose = -A) (hB : B.transpose = -B) :
    (xs.map (fun e => 2*e+1)).sum ≤ Fintype.card n := by
  obtain ⟨r,basis,d,hdegree,hlead,hperm⟩ := hmin
  let V := polynomialKernelBasisMatrix (affineMatrixPencil A B) basis
  have hW : Function.Injective (mixedKernelCoefficientMatrix V d).mulVec :=
    mixed_kernel_basis_coefficients_injective A B basis d hdegree hlead
  have hL := mixed_kernel_basis_pairing_surjective A B basis d hA hdegree hlead
  have hLW := mixed_kernel_pairing_annihilates_coefficients d A B V hA hB
    (polynomialKernelBasisMatrix_mul _ basis)
  have hh := coefficient_pairing_dimension_bound (mixedKernelCoefficientMatrix V d)
    (mixedKernelPairingMatrix A V d) hW hL hLW
  have he := (hperm.map (fun e => 2*e+1)).sum_eq
  rw [← he]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  simp only [Fintype.card_sigma,Fintype.card_fin,← Finset.sum_add_distrib] at hh
  convert hh using 1
  congr 1
  funext j
  omega

end FD56
