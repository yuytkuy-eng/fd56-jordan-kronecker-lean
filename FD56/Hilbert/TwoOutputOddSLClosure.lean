/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TwoDegreeClosure
import FD56.Hilbert.FiveTwoSLNullity
import FD56.Hilbert.MixedSLKronecker

/-! A single bounded-kernel vanishing statement closes the odd-state two-output SL family. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_two_output_odd_sl_nullity (q : ℕ) (hq : 0<q)
    (i₀ : Fin (2*q+1)) :
    Module.finrank (GenericPencilField K (Fin (2*q+1)) (Fin 2))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix
        (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
        (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀).map
          (algebraMap _ (GenericPencilField K (Fin (2*q+1)) (Fin 2)))))) = 2 := by
  have h := generic_affine_sl_nullity_from_observability (K := K) (q-1) 1
    (n := Fin (2*q+1)) (m := Fin 2) (by simp only [Fintype.card_fin]; omega)
    (by omega) (by simp) i₀
    (algebraMap _ (GenericPencilField K (Fin (2*q+1)) (Fin 2)))
    (IsFractionRing.injective _ _)
  simpa using h

theorem generic_two_output_odd_sl_degrees_of_vanishing
    (q : ℕ) (hq : 0<q) (i₀ : Fin (2*q+1))
    (hzero : slHilbert (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) (q*(q+2)-1)=0) :
    HasMinimalKernelDegrees (slKirillovMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] := by
  let M := genericAffineSquare K (Fin (2*q+1)) (Fin 2)
  let P := genericAffineRows K (Fin (2*q+1)) (Fin 2)
  let A := fun i j => (slKirillovMatrix M P i₀ i j).coeff 0
  let B := fun i j => (slKirillovMatrix M P i₀ i j).coeff 1
  have he : affineMatrixPencil A B=slKirillovMatrix M P i₀ :=
    affineMatrixPencil_coefficients _ (slKirillovMatrix_degreeBound M P i₀ 1
      (genericAffineSquare_degree _ _ _) (genericAffineRows_degree _ _ _))
  obtain ⟨r,Bas,e,hZ,hlead,_,_⟩ := polynomial_kernel_has_minimal_basis (slKirillovMatrix M P i₀)
  have hm : HasMinimalKernelDegrees (slKirillovMatrix M P i₀) (List.ofFn e) :=
    ⟨r,Bas,e,hZ,hlead,List.Perm.refl _⟩
  have hl : (List.ofFn e).length=2 :=
    ((slKirillovMatrix_hasMinimalKernelDegrees_iff M P i₀ _).mp hm).length_eq_fraction_nullity
      (F := GenericPencilField K (Fin (2*q+1)) (Fin 2)) |>.trans
        (generic_two_output_odd_sl_nullity q hq i₀)
  have hp : 0<q*(q+2) := Nat.mul_pos hq (by omega)
  have hc : Fintype.card (SLChartInput (Fin (2*q+1)) (Fin 2) i₀)=4*(q*(q+2)-1)+6 := by
    simp only [slChartInput_card,SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    rw [show (2*q+1)*(2*q+1)+(2*q+1)*2=4*(q*(q+2))+3 by ring]
    have hs : q*(q+2)-1+1=q*(q+2) := Nat.sub_add_cancel hp
    omega
  have hz : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (2*q+1)) (Fin 2)))
      (polynomialKernelAtDegree (affineMatrixPencil A B) (q*(q+2)-1))=0 := by
    rw [he,slKirillovMatrix_polynomialKernelAtDegree_finrank,← slHilbert_eq_matrix_kernel]
    exact hzero
  have hx := skew_pencil_two_degrees_of_kernel_vanishing A B (q*(q+2)-1) (List.ofFn e)
    (he.symm ▸ hm) hl hc (slKirillovMatrix_coefficient_skew M P i₀ 0)
    (slKirillovMatrix_coefficient_skew M P i₀ 1) hz
  rw [Nat.sub_add_cancel (by omega : 1≤q*(q+2))] at hx
  exact hx ▸ hm

theorem generic_two_output_odd_sl_kronecker_of_vanishing
    (q : ℕ) (hq : 0<q) (i₀ : Fin (2*q+1))
    (hzero : slHilbert (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) (q*(q+2)-1)=0) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (2*q+1)) (Fin 2))
      (genericAffineRows K (Fin (2*q+1)) (Fin 2)) i₀) [q*(q+2),q*(q+2)] := by
  apply slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree _ _ _) (genericAffineRows_degree _ _ _)
    ((slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mp
      (generic_two_output_odd_sl_degrees_of_vanishing q hq i₀ hzero))
  simp [slChartInput_card,SLInput]
  rw [show (2*q+1)*(2*q+1)+(2*q+1)*2=4*(q*(q+2))+3 by ring]
  omega

end FD56
