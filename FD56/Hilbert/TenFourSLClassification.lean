/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLCertificate
import FD56.Hilbert.TenFourSLBounds
import FD56.Hilbert.TenFourSLLeading
import FD56.Hilbert.TenFourSLNullity
import FD56.Hilbert.KernelDegreesFromBezout
import FD56.Hilbert.TenFourSLTransfer

/-! The characteristic-zero generic SL pencil with ten states and four outputs
has three Kronecker blocks of dimension 27 and two of dimension 29. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem tenFour_sl_witness_minimal_degrees (i₀ : Fin 10) :
    HasMinimalKernelDegrees (slEquationMatrix (tenFourM (K:=K)) tenFourP i₀)
      [13,13,13,14,14] := by
  let L : Matrix (Fin 5) (SLInput (Fin 10) (Fin 4)) K[X] :=
    C ((tenFourLeftScale : K)⁻¹) • tenFourLeft
  have hL : (L*tenFourZ (K:=K) : Matrix (Fin 5) (Fin 5) K[X])=1 := by
    dsimp only [L]
    rw [Matrix.smul_mul,tenFour_left_scaled,smul_smul,← C_mul,
      inv_mul_cancel₀ (by norm_num [tenFourLeftScale]),C_1,one_smul]
  have h := minimal_degrees_of_left_inverse_and_nullity
    (algebraMap K[X] (RatFunc K)) (IsFractionRing.injective K[X] (RatFunc K))
    (slEquationMatrix (tenFourM (K:=K)) tenFourP i₀) tenFourZ L hL
    (tenFour_SL_kernel i₀) (tenFour_sl_fraction_nullity i₀)
    tenFourDegrees tenFour_column_degrees tenFour_leading_injective
  simpa [tenFourDegrees,List.ofFn_succ] using h

theorem generic_ten_four_sl_minimal_and_kronecker (i₀ : Fin 10) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 10) (Fin 4))
      (genericAffineRows K (Fin 10) (Fin 4)) i₀) [13,13,13,14,14] ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 10) (Fin 4))
      (genericAffineRows K (Fin 10) (Fin 4)) i₀) [13,13,13,14,14] :=
  generic_ten_four_sl_classification_of_witness tenFourM tenFourP
    tenFourM_degree tenFourP_degree (tenFour_sl_witness_minimal_degrees 9) i₀

theorem generic_ten_four_sl_hilbert (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin 10) (Fin 4))
      (genericAffineRows K (Fin 10) (Fin 4)) d=3*(d-12)+2*(d-13) := by
  rw [slHilbert_eq_matrix_kernel _ _ (0 : Fin 10),
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_ten_four_sl_minimal_and_kronecker (K:=K) 0).1]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

end FD56
