/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.OneOutputSLVanishing
import FD56.Hilbert.OneDegreeClosure
import FD56.Hilbert.MixedSLKronecker

/-! Complete one-output generic SL classification over every field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_one_output_sl_degrees_of_vanishing
    (N : ℕ) (hN : 2 ≤ N) (i₀ : Fin N)
    (hzero : slHilbert (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1)) (oneOutputWeight N-2)=0) :
    HasMinimalKernelDegrees (slKirillovMatrix
      (genericAffineSquare K (Fin N) (Fin 1)) (genericAffineRows K (Fin N) (Fin 1)) i₀)
      [oneOutputWeight N-1] := by
  let M := genericAffineSquare K (Fin N) (Fin 1)
  let P := genericAffineRows K (Fin N) (Fin 1)
  let A := fun i j => (slKirillovMatrix M P i₀ i j).coeff 0
  let B := fun i j => (slKirillovMatrix M P i₀ i j).coeff 1
  have he : affineMatrixPencil A B=slKirillovMatrix M P i₀ :=
    affineMatrixPencil_coefficients _ (slKirillovMatrix_degreeBound M P i₀ 1
      (genericAffineSquare_degree _ _ _) (genericAffineRows_degree _ _ _))
  obtain ⟨r,Bas,e,hZ,hlead,_,_⟩ := polynomial_kernel_has_minimal_basis (slKirillovMatrix M P i₀)
  have hm : HasMinimalKernelDegrees (slKirillovMatrix M P i₀) (List.ofFn e) :=
    ⟨r,Bas,e,hZ,hlead,List.Perm.refl _⟩
  have hl : (List.ofFn e).length=1 :=
    ((slKirillovMatrix_hasMinimalKernelDegrees_iff M P i₀ _).mp hm).length_eq_fraction_nullity
      (F := GenericPencilField K (Fin N) (Fin 1)) |>.trans
        (generic_one_output_sl_nullity N hN i₀)
  have hp := oneOutputWeight_three_le N hN
  have hs : N*N+N=2*oneOutputWeight N := by nlinarith [oneOutputWeight_twice N]
  have hc : Fintype.card (SLChartInput (Fin N) (Fin 1) i₀)=2*(oneOutputWeight N-2)+3 := by
    simp only [slChartInput_card,SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,mul_one]
    omega
  have hz : Module.finrank (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1)))
      (polynomialKernelAtDegree (affineMatrixPencil A B) (oneOutputWeight N-2))=0 := by
    rw [he,slKirillovMatrix_polynomialKernelAtDegree_finrank,← slHilbert_eq_matrix_kernel]
    exact hzero
  have hx := skew_pencil_one_degree_of_kernel_vanishing A B (oneOutputWeight N-2) (List.ofFn e)
    (he.symm ▸ hm) hl hc (slKirillovMatrix_coefficient_skew M P i₀ 0)
    (slKirillovMatrix_coefficient_skew M P i₀ 1) hz
  rw [show oneOutputWeight N-2+1=oneOutputWeight N-1 by omega] at hx
  exact hx ▸ hm

theorem generic_one_output_sl_kirillov_minimal_degrees
    (N : ℕ) (hN : 0 < N) (i₀ : Fin N) :
    HasMinimalKernelDegrees (slKirillovMatrix
      (genericAffineSquare K (Fin N) (Fin 1)) (genericAffineRows K (Fin N) (Fin 1)) i₀)
      [N*(N+1)/2-1] := by
  by_cases h : N=1
  · subst N
    have hi : i₀=0 := Subsingleton.elim _ _
    subst i₀
    apply (slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mpr
    simpa using generic_square_sl_minimal_degrees (K := K) 1 (by decide)
  · rw [← oneOutputWeight_eq]
    exact generic_one_output_sl_degrees_of_vanishing N (by omega) i₀
      (generic_one_output_sl_critical_vanishing N (by omega))

theorem generic_one_output_sl_minimal_degrees
    (N : ℕ) (hN : 0 < N) (i₀ : Fin N) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin N) (Fin 1)) (genericAffineRows K (Fin N) (Fin 1)) i₀)
      [N*(N+1)/2-1] :=
  (slKirillovMatrix_hasMinimalKernelDegrees_iff _ _ _ _).mp
    (generic_one_output_sl_kirillov_minimal_degrees N hN i₀)

theorem generic_one_output_sl_hilbert (N : ℕ) (hN : 0 < N) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1)) d = d+1-(N*(N+1)/2-1) := by
  rw [slHilbert_eq_matrix_kernel _ _ (⟨0,hN⟩ : Fin N) d,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_one_output_sl_minimal_degrees N hN ⟨0,hN⟩)]
  simp

theorem generic_one_output_sl_kronecker_decomposition
    (N : ℕ) (hN : 0 < N) (i₀ : Fin N) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin N) (Fin 1)) (genericAffineRows K (Fin N) (Fin 1)) i₀)
      [N*(N+1)/2-1] := by
  apply slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree _ _ _) (genericAffineRows_degree _ _ _)
    (generic_one_output_sl_minimal_degrees N hN i₀)
  have hs : N*N+N=2*oneOutputWeight N := by nlinarith [oneOutputWeight_twice N]
  have hp : 0 < oneOutputWeight N := by nlinarith
  rw [← oneOutputWeight_eq]
  simp only [slChartInput_card,SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,mul_one]
  omega

end FD56
