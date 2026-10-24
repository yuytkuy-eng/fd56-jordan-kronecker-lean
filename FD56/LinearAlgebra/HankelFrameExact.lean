/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelFrameKernel

/-! Exactness of the evaluated frame over a commutative coefficient ring. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] [Nontrivial R] {b c : ℕ}

def hankelKernelCoordinates (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (z : R) (v : Fin b → R) : Fin c ⊕ Fin b → R :=
  hankelFrameParameters h g a
    (fun i => (X-C z)*hankelKernelPolynomial h g B z v i)

theorem hankelKernelPolynomial_shift_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hg : ∀ i, 0 < g i) (z : R) (v : Fin b → R) (i : Fin c) :
    ((X-C z)*hankelKernelPolynomial h g B z v i).natDegree ≤ g i := by
  exact hankelCoefficientPolynomial_shift_natDegree g _ i z

theorem hankelKernelCoordinates_reconstruct (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hg : ∀ i, 0<g i) (z : R) (v : Fin b → R) :
    hankelFrame h g a B *ᵥ (fun w => C (hankelKernelCoordinates h g a B z v w)) =
      fun i => (X-C z)*hankelKernelPolynomial h g B z v i := by
  apply hankelFrame_reconstruct h g a B hBH
  · exact hankelKernelPolynomial_shift_degree h g B hg z v
  · exact hankelKernelPolynomial_shift_zero h g a B hHB z v

theorem hankelFrame_mulVec_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (x : Fin c ⊕ Fin b → R) (i : Fin c) :
    ((hankelFrame h g a B *ᵥ fun w => C (x w)) i).natDegree ≤ g i := by
  simp only [Matrix.mulVec, dotProduct]
  apply natDegree_sum_le_of_forall_le
  intro w _
  exact (natDegree_mul_C_le _ _).trans (hankelFrame_degree h g a B i w)

theorem hankelFrame_evaluated_exact (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i)
    (z : R) (x : Fin c ⊕ Fin b → R) :
    (∀ i, ((hankelFrame h g a B *ᵥ fun w => C (x w)) i).eval z=0) ↔
      ∃! v : Fin b → R, x=hankelKernelCoordinates h g a B z v := by
  let p := hankelFrame h g a B *ᵥ fun w => C (x w)
  have hp := hankelFrame_mulVec_degree h g a B x
  have hz : ∀ j r, r+1<h j →
      polynomialHankelAction (fun i => g i+1) a p j r=0 := by
    intro j r hr
    rw [polynomialHankelAction_mulVec]
    simp_rw [hankelFrame_action_zero h g a B hHB j r hr]
    simp
  have he := hankelFrame_evaluation_zero_iff h g a B hBH hHB hh hg p z hp hz
  have hc (v : Fin b → R) :
      p=(fun i => (X-C z)*hankelKernelPolynomial h g B z v i) ↔
        x=hankelKernelCoordinates h g a B z v := by
    rw [← hankelKernelCoordinates_reconstruct h g a B hBH hHB hg z v]
    exact (hankelFrame_constant_parameters_injective h g a B hHB hh).eq_iff
  simpa only [hc] using he

end FD56
