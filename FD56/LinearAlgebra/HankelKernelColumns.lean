/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelFramePolynomial

/-! Explicit columns for the polynomial kernel of the Hankel frame. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] [Nontrivial R] {b c : ℕ}

theorem hankelKernelCoordinates_left (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (z : R) (v : Fin b → R) (i : Fin c) (hi : 0<g i) :
    hankelKernelCoordinates h g a B z v (Sum.inl i) =
      (B *ᵥ fun jr => z^jr.2.val*v jr.1) ⟨i,⟨g i-1,by omega⟩⟩ := by
  exact hankelCoefficientPolynomial_shift_top g _ i z hi

theorem hankelKernelCoordinates_right (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hHB : blockHankel h g a*B=1)
    (z : R) (v : Fin b → R) (j : Fin b) (hj : 0<h j) :
    hankelKernelCoordinates h g a B z v (Sum.inr j) =
      polynomialHankelAction g a (hankelKernelPolynomial h g B z v) j (h j) -
        z^(h j)*v j := by
  change polynomialHankelAction (fun i => g i+1) a
    (fun i => (X-C z)*hankelKernelPolynomial h g B z v i) j (h j-1) = _
  rw [polynomialHankelAction_shift g a (hankelKernelPolynomial h g B z v) z (hankelCoefficientPolynomial_top_coeff g _) j]
  have he := hankelKernelPolynomial_action h g a B hHB z v j ⟨h j-1,by omega⟩
  dsimp only at he
  rw [he,show h j-1+1=h j by omega]
  rw [← mul_assoc,← pow_succ',show h j-1+1=h j by omega]

def hankelInverseColumn (h : Fin b → ℕ) (g : Fin c → ℕ)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (is : Σ i, Fin (g i)) (j : Fin b) : R[X] :=
  ∑ r : Fin (h j), monomial r.val (B is ⟨j,r⟩)

theorem hankelInverseColumn_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (is : Σ i, Fin (g i)) (j : Fin b) (hj : 0<h j) :
    (hankelInverseColumn h g B is j).natDegree < h j := by
  have he : (hankelInverseColumn h g B is j).natDegree ≤ h j-1 := by
    apply natDegree_sum_le_of_forall_le
    intro r _
    exact (natDegree_monomial_le _).trans (by have := r.isLt; omega)
  omega

theorem hankelInverseColumn_mulVec (h : Fin b → ℕ) (g : Fin c → ℕ)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (v : Fin b → R[X]) (is : Σ i, Fin (g i)) :
    (B.map C *ᵥ fun jr => X^jr.2.val*v jr.1) is =
      ∑ j, hankelInverseColumn h g B is j * v j := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sigma,Matrix.map_apply,
    hankelInverseColumn,Finset.sum_mul,← C_mul_X_pow_eq_monomial,mul_assoc]

def hankelKernelMatrix (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hg : ∀ i, 0<g i) : Matrix (Fin c ⊕ Fin b) (Fin b) R[X] :=
  fun w l => match w with
  | Sum.inl i => hankelInverseColumn h g B ⟨i,⟨g i-1,by have := hg i; omega⟩⟩ l
  | Sum.inr j =>
      (∑ i, ∑ s : Fin (g i), C (a j i (h j+s.val))*hankelInverseColumn h g B ⟨i,s⟩ l) -
        if j=l then X^(h l) else 0

theorem hankelPolynomialKernelParameters_eq_mulVec (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hHB : blockHankel h g a*B=1) (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i)
    (v : Fin b → R[X]) :
    hankelPolynomialKernelParameters h g a B v = hankelKernelMatrix h g a B hg *ᵥ v := by
  have hHB' : blockHankel h g (fun j i r => C (a j i r))*B.map C=1 := by
    have he := congrArg (fun M => Matrix.map M (C : R →+* R[X])) hHB
    dsimp only at he
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero C) (map_one C)] at he
    exact he
  funext w
  cases w with
  | inl i =>
    rw [hankelPolynomialKernelParameters,hankelKernelCoordinates_left _ _ _ _ _ _ _ (hg i),
      hankelInverseColumn_mulVec]
    rfl
  | inr j =>
    rw [hankelPolynomialKernelParameters,hankelKernelCoordinates_right _ _ _ _ hHB' _ _ _ (hh j)]
    simp only [polynomialHankelAction,hankelKernelPolynomial,
      hankelCoefficientPolynomial_coeff]
    simp_rw [hankelInverseColumn_mulVec]
    simp only [Matrix.mulVec,dotProduct,hankelKernelMatrix,sub_mul,Finset.sum_sub_distrib]
    simp only [Finset.mul_sum,← mul_assoc]
    congr 1
    · conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    · simp

theorem hankelKernelMatrix_exact (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (x : Fin c ⊕ Fin b → R[X]) :
    hankelFrame h g a B *ᵥ x=0 ↔ ∃! v : Fin b → R[X], x=hankelKernelMatrix h g a B hg *ᵥ v := by
  simpa only [hankelPolynomialKernelParameters_eq_mulVec h g a B hHB hh hg] using
    hankelFrame_polynomial_exact h g a B hBH hHB hh hg x

end FD56
