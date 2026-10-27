/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Evaluated kernels transport through constant invertible congruences. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n i : Type*} [Field K] [Fintype n] [Fintype i]
  [DecidableEq n] [DecidableEq i]

theorem constant_congruence_kernel_lift (A : Matrix n n K) (B : Matrix i i K)
    (T : Matrix n i K) (S : Matrix i n K) (hTS : T*S=1)
    (hcong : T.transpose*A*T=B) (v : i → K) (hv : B *ᵥ v=0) :
    A *ᵥ (T *ᵥ v)=0 := by
  have h := congrArg S.transpose.mulVec hv
  rw [← hcong] at h
  have hi : S.transpose*T.transpose=1 := by rw [← Matrix.transpose_mul,hTS,Matrix.transpose_one]
  simpa only [← Matrix.mulVec_mulVec,Matrix.mulVec_zero,Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc,hi,Matrix.one_mul] using h

theorem polynomial_constant_congruence_eval (A : Matrix n n K[X]) (B : Matrix i i K[X])
    (T : Matrix n i K) (hcong : (T.map C).transpose*A*T.map C=B) (x : K) :
    T.transpose*A.map (Polynomial.evalRingHom x)*T=B.map (Polynomial.evalRingHom x) := by
  have h := congrArg (fun M => M.map (Polynomial.evalRingHom x)) hcong
  dsimp only at h
  rw [Matrix.map_mul,Matrix.map_mul] at h
  have ht : (T.map C).map (Polynomial.evalRingHom x)=T := by
    funext r s
    simp
  have htt : ((T.map C).transpose).map (Polynomial.evalRingHom x)=T.transpose := by
    funext r s
    simp
  simpa only [ht,htt] using h

theorem polynomial_congruence_kernel_functional (A : Matrix n n K[X]) (B : Matrix i i K[X])
    (T : Matrix n i K) (S : Matrix i n K) (hTS : T*S=1)
    (hcong : (T.map C).transpose*A*T.map C=B) (ell : (n → K) →ₗ[K] K)
    (x : K) (hell : ∀ v, A.map (Polynomial.evalRingHom x) *ᵥ v=0 → ell v=0)
    (v : i → K) (hv : B.map (Polynomial.evalRingHom x) *ᵥ v=0) :
    ell (T *ᵥ v)=0 :=
  hell _ (constant_congruence_kernel_lift _ _ T S hTS
    (polynomial_constant_congruence_eval A B T hcong x) v hv)

end FD56
