/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLNormalForm

/-! Observability constraints propagated through the GL coefficient recurrence. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n]

theorem gl_coefficient_recurrence_annihilation
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (A : ℕ → Matrix n m K[X]) (D : ℕ → Matrix m m K[X])
    (hPA : ∀ j<q, P*A j=0)
    (hrec : ∀ j, j+1<q → M*A (j+1)=A j+A (q-1)*D (j+1))
    (i j : ℕ) (hij : i≤j) (hjq : j<q) : P*M^i*A j=0 := by
  induction i generalizing j with
  | zero => simpa using hPA j hjq
  | succ i ih =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
    have hleft := ih k (by omega) (by omega)
    have hright := ih (q-1) (by omega) (by omega)
    calc
      P*M^(i+1)*A (k+1)=(P*M^i)*(M*A (k+1)) := by
        rw [pow_succ]; simp only [Matrix.mul_assoc]
      _ = (P*M^i)*(A k+A (q-1)*D (k+1)) := by rw [hrec k hjq]
      _ = 0 := by
        rw [Matrix.mul_add,← Matrix.mul_assoc,hleft,hright,Matrix.zero_mul,add_zero]

theorem gl_terminal_coefficient_in_observability_kernel
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (A : ℕ → Matrix n m K[X]) (D : ℕ → Matrix m m K[X])
    (hPA : ∀ j<q, P*A j=0)
    (hrec : ∀ j, j+1<q → M*A (j+1)=A j+A (q-1)*D (j+1)) :
    observabilityMatrix M P q*A (q-1)=0 := by
  funext i j
  change ((P*M^i.1.val)*A (q-1)) i.2 j=0
  exact congrFun (congrFun
    (gl_coefficient_recurrence_annihilation M P q A D hPA hrec i.1.val (q-1)
      (by have := i.1.isLt; omega) (by have := i.1.isLt; omega)) i.2) j

theorem gl_terminal_coefficient_factor
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (A : ℕ → Matrix n m K[X]) (D : ℕ → Matrix m m K[X])
    (hPA : ∀ j<q, P*A j=0)
    (hrec : ∀ j, j+1<q → M*A (j+1)=A j+A (q-1)*D (j+1)) :
    ∃ E : Matrix r m K[X], A (q-1)=polynomialKernelBasisMatrix _ B*E :=
  matrix_factor_through_kernel_basis _ B (A (q-1))
    (gl_terminal_coefficient_in_observability_kernel M P q A D hPA hrec)

theorem gl_terminal_beta_parameter
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (A : ℕ → Matrix n m K[X]) (D : ℕ → Matrix m m K[X])
    (hPA : ∀ j<q, P*A j=0)
    (hrec : ∀ j, j+1<q → M*A (j+1)=A j+A (q-1)*D (j+1))
    (hAF : A (q-1)*(P*M^q*polynomialKernelBasisMatrix _ B)=0) :
    ∃! E : Matrix r m K[X],
      A (q-1)=polynomialKernelBasisMatrix _ B*E ∧
      E*(P*M^q*polynomialKernelBasisMatrix _ B)=0 := by
  obtain ⟨E,hE⟩ := gl_terminal_coefficient_factor M P q B A D hPA hrec
  have hV := polynomialKernelBasisMatrix_injective (observabilityMatrix M P q) B
  refine ⟨E,⟨hE,?_⟩,?_⟩
  · apply matrix_left_mul_injective_of_mulVec _ hV
    rw [hE] at hAF
    simpa only [Matrix.mul_assoc,Matrix.mul_zero] using hAF
  · intro E' hE'
    exact matrix_left_mul_injective_of_mulVec _ hV (hE'.1.symm.trans hE)

end FD56
