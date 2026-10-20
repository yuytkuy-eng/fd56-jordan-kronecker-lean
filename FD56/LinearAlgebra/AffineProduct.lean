/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import FD56.LinearAlgebra.PolynomialBezout
import Mathlib.Algebra.Polynomial.Inductions

/-! Independent coefficient columns make multiplication by an affine matrix
surjective between successive degree truncations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K l m n : Type*} [Field K] [Fintype m]

def affineCoefficientColumns (P : Matrix m n K[X]) : Matrix m (n ⊕ n) K :=
  fun i j => Sum.elim (fun j => (P i j).coeff 0) (fun j => (P i j).coeff 1) j

theorem affine_dual_matrices [Fintype n] [DecidableEq n] [DecidableEq m]
    (P : Matrix m n K[X]) (hP : DegreeBound P 1)
    (hJ : Function.Injective (affineCoefficientColumns P).mulVec) :
    ∃ R₀ R₁ : Matrix n m K, R₀.map Polynomial.C * P = 1 ∧
      R₁.map Polynomial.C * P = (Polynomial.X : K[X]) • (1 : Matrix n n K[X]) := by
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective (affineCoefficientColumns P) hJ
  let R₀ : Matrix n m K := fun i j => L (.inl i) j
  let R₁ : Matrix n m K := fun i j => L (.inr i) j
  refine ⟨R₀, R₁, ?_, ?_⟩
  · funext i j
    apply Polynomial.ext
    intro k
    rcases k with _ | k
    · have hh := congrArg (fun A : Matrix (n ⊕ n) (n ⊕ n) K => A (.inl i) (.inl j)) hL
      by_cases hij : i = j <;> simpa [Matrix.mul_apply, affineCoefficientColumns, R₀,
        Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Matrix.one_apply, Polynomial.coeff_one, Polynomial.coeff_X, hij] using hh
    · rcases k with _ | k
      · have hh := congrArg (fun A : Matrix (n ⊕ n) (n ⊕ n) K => A (.inl i) (.inr j)) hL
        by_cases hij : i = j <;> simpa [Matrix.mul_apply, affineCoefficientColumns, R₀,
          Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Matrix.one_apply, Polynomial.coeff_one, Polynomial.coeff_X, hij] using hh
      · have hz (a : m) : (P a j).coeff (k + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP a j) (by omega))
        by_cases hij : i = j <;> simp [Matrix.mul_apply, Polynomial.finset_sum_coeff, hz, Matrix.one_apply, Polynomial.coeff_one, Polynomial.coeff_X, hij]
  · funext i j
    apply Polynomial.ext
    intro k
    rcases k with _ | k
    · have hh := congrArg (fun A : Matrix (n ⊕ n) (n ⊕ n) K => A (.inr i) (.inl j)) hL
      by_cases hij : i = j <;> simpa [Matrix.mul_apply, affineCoefficientColumns, R₁,
        Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Matrix.one_apply, Polynomial.coeff_one, Polynomial.coeff_X, hij] using hh
    · rcases k with _ | k
      · have hh := congrArg (fun A : Matrix (n ⊕ n) (n ⊕ n) K => A (.inr i) (.inr j)) hL
        by_cases hij : i = j <;> simpa [Matrix.mul_apply, affineCoefficientColumns, R₁,
          Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Matrix.one_apply, Polynomial.coeff_one, Polynomial.coeff_X, hij] using hh
      · have hz (a : m) : (P a j).coeff (k + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hP a j) (by omega))
        by_cases hij : i = j <;> simp [Matrix.mul_apply, Polynomial.finset_sum_coeff, hz, Matrix.one_apply, Polynomial.coeff_one, Polynomial.coeff_X, hij]

def boundedRightProduct (P : Matrix m n K[X]) (hP : DegreeBound P 1) (d : ℕ) :
    BoundedMatrix K l m d →ₗ[K] BoundedMatrix K l n (d + 1) where
  toFun U i j := boundedPolyOf ((entries U * P) i j)
    (degreeBound_mul (entries_degree U) hP i j)
  map_add' U V := by
    funext i j
    apply Subtype.ext
    exact congrArg (fun W : Matrix l n K[X] => W i j) (Matrix.add_mul (entries U) (entries V) P)
  map_smul' c U := by
    funext i j
    apply Subtype.ext
    exact congrArg (fun W : Matrix l n K[X] => W i j) (Matrix.smul_mul c (entries U) P)

theorem boundedRightProduct_surjective [Fintype n] [DecidableEq n]
    (P : Matrix m n K[X]) (hP : DegreeBound P 1)
    (R₀ R₁ : Matrix n m K)
    (hR₀ : R₀.map Polynomial.C * P = 1)
    (hR₁ : R₁.map Polynomial.C * P = (Polynomial.X : K[X]) • (1 : Matrix n n K[X])) (d : ℕ) :
    Function.Surjective (boundedRightProduct (l := l) P hP d) := by
  intro W
  let W₀ : Matrix l n K[X] := fun i j => Polynomial.C ((W i j).val.coeff 0)
  let W₁ : Matrix l n K[X] := fun i j => (W i j).val.divX
  let U : Matrix l m K[X] := W₀ * R₀.map Polynomial.C + W₁ * R₁.map Polynomial.C
  have hW₀ : DegreeBound W₀ d := by intro i j; exact (by simp [W₀])
  have hW₁ : DegreeBound W₁ d := by
    intro i j
    have hh := boundedPoly_degree (d + 1) (W i j)
    simp only [W₁, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hR (R : Matrix n m K) : DegreeBound (R.map Polynomial.C) 0 := by
    intro i j
    simp
  have hU : DegreeBound U d := by
    intro i j
    apply Polynomial.natDegree_add_le_of_degree_le
    · simpa using degreeBound_mul hW₀ (hR R₀) i j
    · simpa using degreeBound_mul hW₁ (hR R₁) i j
  refine ⟨fun i j => boundedPolyOf (U i j) (hU i j), ?_⟩
  have he : U * P = entries W := by
    dsimp only [U]
    rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hR₀, hR₁,
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one]
    funext i j
    exact (add_comm _ _).trans (Polynomial.X_mul_divX_add (W i j).val)
  funext i j
  apply Subtype.ext
  exact congrArg (fun V : Matrix l n K[X] => V i j) he

theorem boundedRightProduct_kernel_finrank [Fintype l] [Fintype n] [DecidableEq n]
    (P : Matrix m n K[X]) (hP : DegreeBound P 1)
    (R₀ R₁ : Matrix n m K)
    (hR₀ : R₀.map Polynomial.C * P = 1)
    (hR₁ : R₁.map Polynomial.C * P = (Polynomial.X : K[X]) • (1 : Matrix n n K[X])) (d : ℕ) :
    Module.finrank K (LinearMap.ker (boundedRightProduct (l := l) P hP d)) =
      Fintype.card l * Fintype.card m * (d + 1) -
        Fintype.card l * Fintype.card n * (d + 2) := by
  have hd := (boundedRightProduct (l := l) P hP d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (boundedRightProduct_surjective P hP R₀ R₁ hR₀ hR₁ d),
    finrank_top, boundedMatrix_finrank, boundedMatrix_finrank] at hd
  simp only [Nat.add_assoc] at hd
  exact Nat.eq_sub_of_add_eq (Nat.add_comm _ _ |>.trans hd)

end FD56
