/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CorankOneObservabilityAlpha
import FD56.Hilbert.CorankOneObservabilityDegrees
import FD56.Hilbert.GenericObservabilityGL
import FD56.Hilbert.MixedGLKronecker

/-! One Kronecker block for every odd state dimension with two outputs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem twice_sum_fin_positive (q : ℕ) :
    2 * (∑ i : Fin q, (i.val+1)) = q*(q+1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    rw [Nat.mul_add,ih]
    ring

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_two_output_odd_gl_minimal_degrees (q : ℕ)
    (hm : Fintype.card m = 2) (hn : Fintype.card n = 2*q+1) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) [2*q^2+4*q+1] := by
  cases q with
  | zero =>
    have h := generic_above_gl_minimal_degrees (K := K) (n := n) (m := m) (by omega)
    simpa [hm,hn] using h
  | succ q =>
    obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K := K)
      (n := n) (m := m) (q+1) (by rw [hm,hn]; omega)
    have hα := generic_corank_one_observability_alpha_degrees (K := K)
      (n := n) (m := m) (q+1) (by rw [hm,hn]; omega)
    have hβ : ∀ (r : ℕ) (B : Basis (Fin r)
        (AffineCoefficientField K (MatrixParameters n m))[X]
        (LinearMap.ker (Matrix.toLin' (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) (q+1))))),
        HasMinimalKernelDegrees (genericAffineRows K n m * (genericAffineSquare K n m)^(q+1) *
          polynomialKernelBasisMatrix _ B).transpose
          [Fintype.card m*(∑ i : Fin (q+2), (i.val+1))-(q+2)] := by
      intro r B
      exact generic_corank_one_all_depths_beta_degrees (q+1) (by omega)
        (by rw [hm,hn]; omega) B R hR
    have h := generic_observability_gl_minimal_degrees q (by rw [hm,hn]; omega)
      (by rw [hm,hn]; omega) R hR _ _ hα hβ
    have hβd : (q+2)*(q+2+1)-(q+2) = (q+2)^2 := by
      rw [show (q+2)*(q+2+1)=(q+2)^2+(q+2) by ring,Nat.add_sub_cancel]
    have he : (q+1)*(q+1+1)+(q+2)^2+1+q = 2*(q+1)^2+4*(q+1)+1 := by ring
    simpa only [hm,twice_sum_fin_positive,hβd,degreeConvolution,List.flatMap_cons,
      List.flatMap_nil,List.map_cons,List.map_nil,List.append_nil,he] using h

theorem generic_two_output_odd_gl_kronecker_decomposition (q : ℕ)
    (hm : Fintype.card m = 2) (hn : Fintype.card n = 2*q+1) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) [2*q^2+4*q+1] := by
  apply glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_two_output_odd_gl_minimal_degrees q hm hn)
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,hm,hn,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]
  ring

end FD56
