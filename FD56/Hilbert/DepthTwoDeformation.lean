/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoAuxiliaryLift
import FD56.Hilbert.ConstantEquivalence
import FD56.LinearAlgebra.RankSpecializationExtension
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A transcendental scalar shift makes the depth-two change of stack
invertible while retaining every maximal coefficient rank at the initial point. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L m n r : Type*} [Field K] [Field L]

theorem depthTwo_scalar_shift_isUnit_det [Fintype m] [DecidableEq m]
    (φ : K[X] →+* L) (hφ : Function.Injective φ) (D : Matrix m m K) :
    IsUnit (D.map (φ.comp C) + φ X • (1 : Matrix m m L)).det := by
  have he : (Matrix.charmatrix (-D)).map φ =
      D.map (φ.comp C) + φ X • (1 : Matrix m m L) := by
    funext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.charmatrix_apply_eq, Matrix.map_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply, add_comm]
    · simp [Matrix.charmatrix_apply_ne _ _ _ hij, Matrix.map_apply, Matrix.add_apply,
        Matrix.smul_apply, Matrix.one_apply, hij]
  apply isUnit_iff_ne_zero.mpr
  rw [← he]
  have hd := RingHom.map_det φ (Matrix.charmatrix (-D))
  change φ (Matrix.charmatrix (-D)).det = ((Matrix.charmatrix (-D)).map φ).det at hd
  rw [← hd]
  exact fun h => ((-D).charpoly_monic.ne_zero) (hφ (h.trans (map_zero φ).symm))

def depthTwoPolynomialDeformation (F H : Matrix m r K[X]) : Matrix m r K[X][X] :=
  fun i j => (F i j).map C + Polynomial.C Polynomial.X * (H i j).map C

theorem depthTwoPolynomialDeformation_degree (F H : Matrix m r K[X]) (e : r → ℕ)
    (hF : ∀ i j, (F i j).natDegree ≤ e j)
    (hH : ∀ i j, (H i j).natDegree ≤ e j) :
    ∀ i j, (depthTwoPolynomialDeformation F H i j).natDegree ≤ e j := by
  intro i j
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact Polynomial.natDegree_map_le.trans (hF i j)
  · exact Polynomial.natDegree_mul_le.trans (by
      simpa using (Polynomial.natDegree_map_le (f := C) (p := H i j)).trans (hH i j))

theorem depthTwoPolynomialDeformation_zero (F H : Matrix m r K[X]) :
    (depthTwoPolynomialDeformation F H).map
      (Polynomial.mapRingHom (Polynomial.evalRingHom 0)) = F := by
  have hc : (Polynomial.evalRingHom (0 : K)).comp C = RingHom.id K := by
    ext x
    simp
  funext i j
  simp [depthTwoPolynomialDeformation, Polynomial.map_map, hc]

theorem depthTwoPolynomialDeformation_map (φ : K[X] →+* L)
    (F H : Matrix m r K[X]) :
    (depthTwoPolynomialDeformation F H).map (Polynomial.mapRingHom φ) =
      F.map (Polynomial.mapRingHom (φ.comp C)) +
        Polynomial.C (φ X) • H.map (Polynomial.mapRingHom (φ.comp C)) := by
  funext i j
  simp [depthTwoPolynomialDeformation, Polynomial.map_map, Matrix.smul_apply,
    smul_eq_mul]

theorem depthTwo_deformation_identities [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (P Q : Matrix m n K[X]) (V : Matrix n r K[X])
    (Mf M₀ : Matrix n n K[X]) (A D : Matrix m m K[X]) (c : K[X])
    (hfactor : P * Mf = A * P + D * Q) (hM₀ : P * M₀ = Q)
    (hMfV : P * Mf * V = 0) (hQV : Q * V = 0) :
    P * (Mf + c • M₀) = A * P + (D + c • 1) * Q ∧
      P * (Mf + c • M₀) * V = 0 ∧
      P * (Mf + c • M₀) ^ 2 * V =
        (D + c • 1) * (Q * Mf * V + c • (Q * M₀ * V)) := by
  have hf : P * (Mf + c • M₀) = A * P + (D + c • 1) * Q := by
    rw [Matrix.mul_add, Matrix.mul_smul, hfactor, hM₀,
      Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, add_assoc]
  have hz : P * (Mf + c • M₀) * V = 0 := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul,
      hMfV, hM₀, hQV, smul_zero, add_zero]
  refine ⟨hf, hz, ?_⟩
  rw [depthTwo_terminal_of_factor P Q (Mf + c • M₀) V A (D + c • 1) hf hz]
  congr 1
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul]

theorem depthTwo_deformation_kernel_le [Fintype m] [Fintype r]
    [DecidableEq m] [DecidableEq r]
    (φ : K[X] →+* L) (hφ : Function.Injective φ)
    (F H : Matrix m r K[X]) (e : r → ℕ)
    (hF : ∀ i j, (F i j).natDegree ≤ e j)
    (hH : ∀ i j, (H i j).natDegree ≤ e j) (d : ℕ) :
    Module.finrank L (polynomialKernelAtDegree
      ((depthTwoPolynomialDeformation F H).map (Polynomial.mapRingHom φ)).transpose d) ≤
      Module.finrank K (polynomialKernelAtDegree F.transpose d) := by
  let W := depthTwoPolynomialDeformation F H
  let A := weightedCoefficientMatrix W.transpose (fun _ => d) (fun j => d+e j)
  have hzero : A.map (Polynomial.evalRingHom 0) =
      weightedCoefficientMatrix F.transpose (fun _ => d) (fun j => d+e j) := by
    dsimp only [A, W]
    rw [← weightedCoefficientMatrix_map, Matrix.transpose_map,
      depthTwoPolynomialDeformation_zero]
  have hgen : A.map φ = weightedCoefficientMatrix
      (W.map (Polynomial.mapRingHom φ)).transpose (fun _ => d) (fun j => d+e j) := by
    dsimp only [A]
    rw [← weightedCoefficientMatrix_map, Matrix.transpose_map]
  have h := matrix_kernel_finrank_le_of_field_specialization
    (Polynomial.evalRingHom 0) φ hφ A
  rw [hzero, hgen, weighted_coefficient_kernel_finrank _ _ _ (by
    intro i j
    have hh := (Polynomial.natDegree_map_le (f := φ) (p := W j i)).trans
      (depthTwoPolynomialDeformation_degree F H e hF hH j i)
    change ((W j i).map φ).natDegree + d ≤ d+e i
    omega), weighted_coefficient_kernel_finrank _ _ _ (by
    intro i j
    have hh := hF j i
    change (F j i).natDegree+d≤d+e i
    omega)] at h
  exact h

theorem constant_left_mul_kernel_hilbert [Fintype m] [Fintype r]
    [DecidableEq m] [DecidableEq r]
    (D E : Matrix m m K) (hDE : D * E = 1) (hED : E * D = 1)
    (F : Matrix m r K[X]) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (D.map C * F).transpose d) =
      Module.finrank K (polynomialKernelAtDegree F.transpose d) := by
  apply constant_equivalence_kernel_hilbert F.transpose (D.map C * F).transpose
    1 1 D.transpose E.transpose
  · simp [Matrix.transpose_mul, Matrix.transpose_map]
  · simp only [Matrix.transpose_mul, Matrix.transpose_map, Matrix.map_one,
      map_zero, map_one, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, hED]
    simp
  · rw [← Matrix.transpose_mul, hED, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hDE, Matrix.transpose_one]

end FD56
