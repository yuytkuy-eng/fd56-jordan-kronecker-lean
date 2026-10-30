/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BivariateDiagonalRescaling
import FD56.LinearAlgebra.PolynomialKernelInitialCoefficients
import Mathlib.Algebra.Polynomial.Div

/-! A tail kernel test forces divisibility of every specialized kernel
vector. This is a residue statement, not a periodicity theorem. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K a b : Type*} [Field K] [Fintype b]

theorem polynomial_tail_kernel_residue_divisible
    (Q : Matrix a b K[X][X]) (H : b → K[X][X]) (k : ℕ) (hk : 0<k)
    (hQH : Q*ᵥ(fun j => bivariateDiagonalRescaling (H j))=0)
    (hzero : ∀ z : b → K[X],
      (fun i j => (Q i j).coeff 0)*ᵥz=0 →
      (∀ j, (z j).natDegree≤k-1) → z=0) :
    ∀ j, (X : K[X])^k ∣ (H j).map (Polynomial.evalRingHom 0) := by
  have h := polynomial_kernel_initial_coefficients_zero Q
    (fun j => bivariateDiagonalRescaling (H j)) (k-1) k hQH hzero (by
      intro n hn j
      exact (bivariateDiagonalRescaling_coefficient_degree (H j) n).trans (by omega))
  intro j
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  have hc := congrArg (fun p : K[X] => p.coeff n) (h n hn j)
  dsimp only at hc
  rw [bivariateDiagonalRescaling_diagonal_coeff,Polynomial.coeff_zero] at hc
  simpa only [Polynomial.coeff_map,Polynomial.coe_evalRingHom,
    Polynomial.coeff_zero_eq_eval_zero] using hc

theorem polynomial_kernel_shift_of_residue_divisible
    (P : Matrix a b K[X][X]) (A : Matrix a b K[X]) (H : b → K[X][X])
    (N k d : ℕ)
    (hmain : P.map (Polynomial.mapRingHom (Polynomial.evalRingHom 0))=(X : K[X])^N • A)
    (hPH : P*ᵥH=0)
    (hdiv : ∀ j, (X : K[X])^k ∣ (H j).map (Polynomial.evalRingHom 0))
    (hdeg : ∀ j, (H j).natDegree≤d+k) :
    ∃ z : b → K[X], A*ᵥz=0 ∧ (∀ j, (z j).natDegree≤d) ∧
      (fun j => (H j).map (Polynomial.evalRingHom 0))=(X : K[X])^k • z := by
  classical
  choose z hz using hdiv
  have hres : (fun j => (H j).map (Polynomial.evalRingHom 0))=(X : K[X])^k • z :=
    funext hz
  have hker : (P.map (Polynomial.mapRingHom (Polynomial.evalRingHom 0)))*ᵥ
      (fun j => (H j).map (Polynomial.evalRingHom 0))=0 := by
    funext i
    have h := congrArg (Polynomial.mapRingHom (Polynomial.evalRingHom 0)) (congrFun hPH i)
    simpa [RingHom.map_mulVec,Function.comp_def] using h
  rw [hmain,hres,Matrix.smul_mulVec_assoc,Matrix.mulVec_smul_assoc,smul_smul] at hker
  refine ⟨z,?_,?_,hres⟩
  · funext i
    have h := congrFun hker i
    change X^N*X^k*(A*ᵥz) i=0 at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero
      (pow_ne_zero N Polynomial.X_ne_zero) (pow_ne_zero k Polynomial.X_ne_zero))
  · intro j
    by_cases hj : z j=0
    · simp [hj]
    · have hd : ((H j).map (Polynomial.evalRingHom 0)).natDegree≤d+k :=
        Polynomial.natDegree_map_le.trans (hdeg j)
      rw [hz j,Polynomial.natDegree_mul (pow_ne_zero k Polynomial.X_ne_zero) hj,
        Polynomial.natDegree_X_pow] at hd
      omega

end FD56
