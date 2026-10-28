/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerSLHilbert
import FD56.Hilbert.ScalarCorrectionCriterion

/-! When the top GL multiplicity is at least the scalar degree capacity, a
single bounded scalar obstruction determines the entire SL degree list.
The obstruction is an explicit certificate premise, not a genericity claim. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem sl_three_level_degrees_of_scalar_obstruction
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n)
    (D A B C : ℕ) (hC : D+2≤C)
    (hmin : HasMinimalKernelDegrees (glEquationMatrix M P)
      (List.replicate A D ++ List.replicate B (D+1) ++ List.replicate C (D+2)))
    (hcanon : HasKroneckerDecomposition (glKirillovMatrix M P)
      (List.replicate A D ++ List.replicate B (D+1) ++ List.replicate C (D+2)))
    (htrace : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]),
      P*X=0 → M*X-X*M=U*P → Matrix.trace X=0)
    (hscalar : ∀ (X : Matrix n n K[X]) (U : Matrix n m K[X]) (c : K[X]),
      DegreeBound X D → DegreeBound U D → SLRadical M P X U →
        M*X-X*M=U*P+c • 1 → c=0) :
    HasMinimalKernelDegrees (slEquationMatrix M P i₀)
      (List.replicate A D ++ List.replicate (B+D+3) (D+1) ++
        List.replicate (C-(D+2)) (D+2)) := by
  have hloweq (d : ℕ) (hd : d≤D) : slHilbert M P d=
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) := by
    apply slHilbert_eq_gl_of_scalar_obstruction M P hM hP i₀ d htrace
    intro X U c hX hU hr hc
    exact hscalar X U c (fun i j => (hX i j).trans hd)
      (fun i j => (hU i j).trans hd) hr hc
  have hlow (d : ℕ) (hd : d<D) :
      Module.finrank K (polynomialKernelAtDegree (slEquationMatrix M P i₀) d)=0 := by
    rw [← slHilbert_eq_matrix_kernel,hloweq d hd.le,
      (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d]
    simp only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,
      smul_eq_mul]
    have h0 : d+1-D=0 := by omega
    have h1 : d+1-(D+1)=0 := by omega
    have h2 : d+1-(D+2)=0 := by omega
    simp only [h0,h1,h2,mul_zero,add_zero]
  have hcritical : Module.finrank K
      (polynomialKernelAtDegree (slEquationMatrix M P i₀) D)=A+(D+2-C) := by
    rw [← slHilbert_eq_matrix_kernel,hloweq D le_rfl,
      (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin D]
    simp only [List.map_append,List.map_replicate,List.sum_append,List.sum_replicate,
      smul_eq_mul,Nat.add_sub_cancel_left,Nat.add_sub_cancel,Nat.sub_self,
      show D+1-(D+2)=0 by omega,show D+2-C=0 by omega,mul_zero,mul_one,add_zero]
  have hhigh (d : ℕ) (hd : D<d) :
      Module.finrank K (polynomialKernelAtDegree (slEquationMatrix M P i₀) d)=
        Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d)+(d+2) := by
    rw [← slHilbert_eq_matrix_kernel]
    apply slHilbert_high_of_gl_kronecker M P hM hP i₀ _ hcanon htrace d
    intro e he
    simp only [List.mem_append,List.mem_replicate] at he
    rcases he with (⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩ <;> omega
  have h := hasMinimalKernelDegrees_three_of_scalar_correction
    (slEquationMatrix M P i₀) (glEquationMatrix M P) D A B C
    (by omega) hmin hlow hcritical hhigh
  simpa only [show D+2-C=0 by omega,Nat.add_zero,Nat.mul_zero,Nat.sub_zero] using h

end FD56
