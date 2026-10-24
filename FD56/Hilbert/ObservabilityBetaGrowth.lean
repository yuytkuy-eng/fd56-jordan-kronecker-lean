/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTerminalObservability
import FD56.Hilbert.KernelGrowth
import FD56.LinearAlgebra.RowNormalization

/-! Evaluation bounds for terminal auxiliary kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K m n r : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype m] [DecidableEq m] [DecidableEq r] in
theorem terminal_kernel_transfer_eval_injective
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (x : K)
    (hO : Function.Injective ((observabilityMatrix M P (q+1)).map
      (Polynomial.evalRingHom x)).mulVec) :
    Function.Injective ((P*M^q*polynomialKernelBasisMatrix
      (observabilityMatrix M P q) B).map (Polynomial.evalRingHom x)).mulVec := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  let φ := Polynomial.evalRingHom x
  have hzero (i : Fin q) : P*M^i.val*V=0 := by
    funext y j
    exact congrFun (congrFun (polynomialKernelBasisMatrix_mul _ B) (i,y)) j
  intro c d h
  apply polynomialKernelBasisMatrix_pointwise_injective _ B x
  apply hO
  funext ix
  rcases ix with ⟨i,y⟩
  change (((P*M^i.val).map φ) *ᵥ (V.map φ *ᵥ c)) y =
    (((P*M^i.val).map φ) *ᵥ (V.map φ *ᵥ d)) y
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,← Matrix.map_mul]
  by_cases hi : i.val < q
  · rw [hzero ⟨i.val,hi⟩,Matrix.map_zero _ (map_zero φ),Matrix.zero_mulVec,Matrix.zero_mulVec]
  · have hiq : i.val=q := by omega
    rw [hiq]
    exact congrFun h y

theorem polynomial_left_kernel_linear_bound (F : Matrix m r K[X])
    (hF : Function.Injective (F.map (Polynomial.evalRingHom 0)).mulVec) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree F.transpose d) ≤
      (Fintype.card m-Fintype.card r)*(d+1) := by
  obtain ⟨L,hL⟩ := matrix_left_inverse_of_injective _ hF
  have hs : Function.Surjective (F.map (Polynomial.evalRingHom 0)).transpose.mulVec := by
    intro v
    refine ⟨L.transpose *ᵥ v,?_⟩
    rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,hL,Matrix.transpose_one,Matrix.one_mulVec]
  have hd := surjective_matrix_kernel_finrank _ hs
  have hh := polynomial_kernel_shift_bound F.transpose 0
    (Fintype.card m-Fintype.card r) (by simpa only [Matrix.transpose_map] using hd.le)
    (by intro k hk; omega) d
  simpa only [Nat.sub_zero] using hh

theorem generic_observability_beta_linear_bound
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q)))) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree
        (genericAffineRows K n m * (genericAffineSquare K n m)^q *
          polynomialKernelBasisMatrix (observabilityMatrix
            (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose d) ≤
      (Fintype.card m-Fintype.card r)*(d+1) :=
  polynomial_left_kernel_linear_bound _
    (terminal_kernel_transfer_eval_injective q _ _ B 0
      (generic_terminal_observability_zero_injective q hmn hnm)) d

end FD56
