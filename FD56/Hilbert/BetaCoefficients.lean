/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BetaKernel
import FD56.Hilbert.WeightedCoefficients
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Finite coefficient matrices for the weighted beta relation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R S K m n : Type*} [CommRing R] [CommRing S] [Field K]

def betaDegrees {m : Type*} (d : ℕ) : m ⊕ m → ℕ :=
  Sum.elim (fun _ => d) (fun _ => d + 1)

def betaEquationMatrix [Fintype n] (M : Matrix n n R[X]) (P : Matrix m n R[X]) :
    Matrix n (m ⊕ m) R[X] :=
  Matrix.fromCols (P * M).transpose (-P.transpose)

def betaCoefficientMatrix [Fintype n] (M : Matrix n n R[X]) (P : Matrix m n R[X])
    (d : ℕ) : Matrix (Σ _ : n, Fin (d + 2 + 1))
      (Σ j : m ⊕ m, Fin (betaDegrees d j + 1)) R :=
  weightedCoefficientMatrix (betaEquationMatrix M P) (betaDegrees d) (fun _ => d + 2)

theorem betaEquationMatrix_map [Fintype n] (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (φ : R →+* S) :
    betaEquationMatrix (M.map (Polynomial.mapRingHom φ)) (P.map (Polynomial.mapRingHom φ)) =
      (betaEquationMatrix M P).map (Polynomial.mapRingHom φ) := by
  apply Matrix.ext
  intro x j
  cases j with
  | inl j =>
    change ((P.map (Polynomial.mapRingHom φ)) * (M.map (Polynomial.mapRingHom φ))) j x =
      Polynomial.map φ ((P * M) j x)
    rw [← Matrix.map_mul]
    rfl
  | inr j => simp [betaEquationMatrix]

theorem betaCoefficientMatrix_map [Fintype n] (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (d : ℕ) (φ : R →+* S) :
    betaCoefficientMatrix (M.map (Polynomial.mapRingHom φ)) (P.map (Polynomial.mapRingHom φ)) d =
      (betaCoefficientMatrix M P d).map φ := by
  rw [betaCoefficientMatrix, betaEquationMatrix_map]
  apply Matrix.ext
  intro i j
  simp [weightedCoefficientMatrix, betaCoefficientMatrix, ← Polynomial.coeff_map,
    Polynomial.map_mul]

theorem betaEquationMatrix_mulVec [Fintype m] [Fintype n]
    (M : Matrix n n R[X]) (P : Matrix m n R[X]) (v : m ⊕ m → R[X]) :
    betaEquationMatrix M P *ᵥ v =
      (P * M).transpose *ᵥ (fun i => v (Sum.inl i)) -
        P.transpose *ᵥ (fun i => v (Sum.inr i)) := by
  funext x
  simp [betaEquationMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    sub_eq_add_neg, Finset.sum_neg_distrib]

theorem beta_weighted_degree_bound [Fintype n] (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    ∀ x j, (betaEquationMatrix M P x j).natDegree + betaDegrees d j ≤ d + 2 := by
  intro x j
  cases j with
  | inl j =>
    have h := degreeBound_mul hP hM j x
    change ((P * M) j x).natDegree + d ≤ d + 2
    omega
  | inr j =>
    change (-P j x).natDegree + (d + 1) ≤ d + 2
    rw [Polynomial.natDegree_neg]
    have h := hP j x
    omega

variable [Fintype m] [Fintype n]

def betaWeightedKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :
    weightedPolynomialKernel (betaEquationMatrix M P) (betaDegrees d) ≃ₗ[K]
      boundedBetaKernel M P d where
  toFun z := ⟨(fun i => z.val (Sum.inl i), fun i => z.val (Sum.inr i)), by
    have hz := z.property
    change betaEquationMatrix M P *ᵥ (fun j => (z.val j).val) = 0 at hz
    rw [betaEquationMatrix_mulVec] at hz
    exact hz⟩
  invFun z := ⟨fun j => match j with
      | Sum.inl i => z.val.1 i
      | Sum.inr i => z.val.2 i, by
    change betaEquationMatrix M P *ᵥ _ = 0
    rw [betaEquationMatrix_mulVec]
    exact z.property⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    cases j <;> rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def betaCoefficientKernelEquiv [DecidableEq m] (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    LinearMap.ker (Matrix.toLin' (betaCoefficientMatrix M P d)) ≃ₗ[K]
      boundedBetaKernel M P d :=
  (weightedCoefficientKernelEquiv (betaEquationMatrix M P) (betaDegrees d) (fun _ => d + 2)
    (beta_weighted_degree_bound M P hM hP d)).trans (betaWeightedKernelEquiv M P d)

theorem beta_coefficient_kernel_finrank [DecidableEq m] (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (betaCoefficientMatrix M P d))) =
      Module.finrank K (boundedBetaKernel M P d) :=
  (betaCoefficientKernelEquiv M P hM hP d).finrank_eq

theorem beta_coefficient_injective_of_kernel_zero [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hz : Module.finrank K (boundedBetaKernel M P d) = 0) :
    Function.Injective (betaCoefficientMatrix M P d).mulVec := by
  apply weighted_coefficient_injective_of_kernel_zero
    (betaEquationMatrix M P) (betaDegrees d) (fun _ => d + 2)
    (beta_weighted_degree_bound M P hM hP d)
  rw [(betaWeightedKernelEquiv M P d).finrank_eq, hz]

theorem beta_kernel_finrank_of_coefficient_injective [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hi : Function.Injective (betaCoefficientMatrix M P d).mulVec) :
    Module.finrank K (boundedBetaKernel M P d) = 0 := by
  rw [← (betaWeightedKernelEquiv M P d).finrank_eq]
  exact weighted_kernel_finrank_of_coefficient_injective
    (betaEquationMatrix M P) (betaDegrees d) (fun _ => d + 2)
    (beta_weighted_degree_bound M P hM hP d) hi

theorem beta_coefficient_surjective_of_kernel_finrank [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hh : Module.finrank K (boundedBetaKernel M P d) + Fintype.card n * (d + 3) =
      Fintype.card m * (d + 1) + Fintype.card m * (d + 2)) :
    Function.Surjective (betaCoefficientMatrix M P d).mulVec := by
  apply weighted_coefficient_surjective_of_kernel_finrank
    (betaEquationMatrix M P) (betaDegrees d) (fun _ => d + 2)
    (beta_weighted_degree_bound M P hM hP d)
  rw [(betaWeightedKernelEquiv M P d).finrank_eq]
  simpa [betaDegrees, Fintype.sum_sum_type, Nat.add_assoc] using hh

theorem beta_kernel_finrank_of_coefficient_surjective [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hs : Function.Surjective (betaCoefficientMatrix M P d).mulVec) :
    Module.finrank K (boundedBetaKernel M P d) =
      (Fintype.card m * (d + 1) + Fintype.card m * (d + 2)) -
        Fintype.card n * (d + 3) := by
  rw [← (betaWeightedKernelEquiv M P d).finrank_eq]
  simpa [betaDegrees, Fintype.sum_sum_type, Nat.add_assoc] using
    weighted_kernel_finrank_of_coefficient_surjective
      (betaEquationMatrix M P) (betaDegrees d) (fun _ => d + 2)
      (beta_weighted_degree_bound M P hM hP d) hs

end FD56
