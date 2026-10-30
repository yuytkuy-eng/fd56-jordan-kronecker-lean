/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix

/-! A bounded kernel test for the constant deformation matrix forces the
initial deformation coefficients of a polynomial kernel vector to vanish.
The inner polynomial variable and the outer deformation variable remain
separate throughout. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

private theorem polynomial_product_coeff_of_lower_zero {R : Type*} [Semiring R]
    (p q : R[X]) (n : ℕ) (hq : ∀ t, t<n → q.coeff t=0) :
    (p*q).coeff n=p.coeff 0*q.coeff n := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_single (0,n)
  · intro ij hij hne
    have hsum : ij.1+ij.2=n := Finset.mem_antidiagonal.mp hij
    have hlt : ij.2<n := by
      by_contra h
      have he : ij=(0,n) := by
        apply Prod.ext <;> omega
      exact hne he
    rw [hq ij.2 hlt,mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_antidiagonal.mpr (Nat.zero_add n)))

theorem polynomial_mulVec_coeff_of_lower_coefficients_zero
    {R a b : Type*} [Semiring R] [Fintype b]
    (P : Matrix a b R[X]) (H : b → R[X]) (n : ℕ)
    (hH : ∀ t, t<n → ∀ j, (H j).coeff t=0) :
    (fun i => ((P*ᵥH) i).coeff n)=
      (fun i j => (P i j).coeff 0)*ᵥ(fun j => (H j).coeff n) := by
  funext i
  change (∑ j, P i j*H j).coeff n=∑ j, (P i j).coeff 0*(H j).coeff n
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  exact polynomial_product_coeff_of_lower_zero (P i j) (H j) n (fun t ht => hH t ht j)

theorem polynomial_kernel_initial_coefficients_zero
    {K a b : Type*} [Field K] [Fintype b]
    (P : Matrix a b K[X][X]) (H : b → K[X][X]) (d k : ℕ)
    (hPH : P*ᵥH=0)
    (hzero : ∀ z : b → K[X],
      (fun i j => (P i j).coeff 0)*ᵥz=0 →
      (∀ j, (z j).natDegree≤d) → z=0)
    (hdeg : ∀ n, n<k → ∀ j, ((H j).coeff n).natDegree≤d) :
    ∀ n, n<k → ∀ j, (H j).coeff n=0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hprevious : ∀ t, t<n → ∀ j, (H j).coeff t=0 := by
      intro t ht
      exact ih t ht (ht.trans hn)
    have hkernel : (fun i j => (P i j).coeff 0)*ᵥ(fun j => (H j).coeff n)=0 := by
      rw [← polynomial_mulVec_coeff_of_lower_coefficients_zero P H n hprevious,hPH]
      funext i
      exact Polynomial.coeff_zero n
    have h := hzero (fun j => (H j).coeff n) hkernel (hdeg n hn)
    exact fun j => congrFun h j

end FD56
