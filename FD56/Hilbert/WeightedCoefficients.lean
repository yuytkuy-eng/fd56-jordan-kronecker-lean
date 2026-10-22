/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Coefficients

/-! Finite coefficient matrices for polynomial systems with different degree
bounds on their input and output coordinates. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R K a b : Type*} [CommRing R] [Field K]

def weightedCoefficientMatrix (P : Matrix a b R[X]) (g : b → ℕ) (h : a → ℕ) :
    Matrix (Σ i, Fin (h i + 1)) (Σ j, Fin (g j + 1)) R :=
  fun ik jl => (P ik.1 jl.1 * Polynomial.X ^ jl.2.val).coeff ik.2.val

def weightedCoefficientPolynomial [DecidableEq R] (g : b → ℕ)
    (v : (Σ j, Fin (g j + 1)) → R) : b → R[X] :=
  fun j => Polynomial.ofFn (g j + 1) (fun l => v ⟨j, l⟩)

theorem weightedCoefficientPolynomial_degree [DecidableEq R] (g : b → ℕ)
    (v : (Σ j, Fin (g j + 1)) → R) (j : b) :
    (weightedCoefficientPolynomial g v j).natDegree ≤ g j :=
  Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)

theorem weightedCoefficientMatrix_mulVec [Fintype b] [DecidableEq R]
    (P : Matrix a b R[X]) (g : b → ℕ) (h : a → ℕ)
    (v : (Σ j, Fin (g j + 1)) → R) (i : a) (k : Fin (h i + 1)) :
    (weightedCoefficientMatrix P g h *ᵥ v) ⟨i, k⟩ =
      ((P *ᵥ weightedCoefficientPolynomial g v) i).coeff k.val := by
  simp only [weightedCoefficientMatrix, Matrix.mulVec, dotProduct,
    weightedCoefficientPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Finset.mul_sum, Polynomial.finset_sum_coeff, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have hh : P i j * Polynomial.monomial l.val (v ⟨j, l⟩) =
      Polynomial.C (v ⟨j, l⟩) * (P i j * Polynomial.X ^ l.val) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    ring
  rw [hh, Polynomial.coeff_C_mul]
  exact mul_comm _ _

theorem weightedCoefficientMatrix_map (P : Matrix a b R[X])
    (g : b → ℕ) (h : a → ℕ) (φ : R →+* K) :
    weightedCoefficientMatrix (P.map (Polynomial.mapRingHom φ)) g h =
      (weightedCoefficientMatrix P g h).map φ := by
  funext i j
  simp [weightedCoefficientMatrix, ← Polynomial.coeff_map, Polynomial.map_mul]

def weightedBoundedKernelMap [Fintype b] (P : Matrix a b K[X]) (g : b → ℕ) :
    (∀ j, BoundedPoly K (g j)) →ₗ[K] (a → K[X]) where
  toFun v := P *ᵥ fun j => (v j).val
  map_add' v w := by
    change P *ᵥ ((fun j => (v j).val) + (fun j => (w j).val)) = _
    exact Matrix.mulVec_add _ _ _
  map_smul' c v := by
    change P *ᵥ (c • (fun j => (v j).val)) = _
    exact Matrix.mulVec_smul _ _ _

def weightedPolynomialKernel [Fintype b] (P : Matrix a b K[X]) (g : b → ℕ) :
    Submodule K (∀ j, BoundedPoly K (g j)) := LinearMap.ker (weightedBoundedKernelMap P g)

theorem weighted_polynomial_mulVec_degree [Fintype b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (v : b → K[X]) (hv : ∀ j, (v j).natDegree ≤ g j) (i : a) :
    ((P *ᵥ v) i).natDegree ≤ h i := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add_left (hv j) _).trans (hP i j))

theorem weighted_coefficient_kernel_zero [Fintype b] [DecidableEq K]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (v : (Σ j, Fin (g j + 1)) → K) (hv : weightedCoefficientMatrix P g h *ᵥ v = 0) :
    P *ᵥ weightedCoefficientPolynomial g v = 0 := by
  funext i
  apply Polynomial.ext
  intro k
  by_cases hk : k < h i + 1
  · have he := congrFun hv ⟨i, ⟨k, hk⟩⟩
    rw [weightedCoefficientMatrix_mulVec] at he
    exact he
  · change ((P *ᵥ weightedCoefficientPolynomial g v) i).coeff k = 0
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
      (weighted_polynomial_mulVec_degree P g h hP _
        (weightedCoefficientPolynomial_degree g v) i) (by omega))

def weightedCoefficientKernelEquiv [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i) :
    LinearMap.ker (Matrix.toLin' (weightedCoefficientMatrix P g h)) ≃ₗ[K]
      weightedPolynomialKernel P g := by
  classical
  exact {
    toFun := fun v => ⟨fun j => boundedPolyOf (weightedCoefficientPolynomial g v.val j)
      (weightedCoefficientPolynomial_degree g v.val j),
      weighted_coefficient_kernel_zero P g h hP v.val v.property⟩
    invFun := fun v => ⟨fun jl => (v.val jl.1).val.coeff jl.2.val, by
      have he : weightedCoefficientPolynomial g
          (fun jl => (v.val jl.1).val.coeff jl.2.val) = fun j => (v.val j).val := by
        funext j
        exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
          (p := (v.val j).val) (n := g j + 1) (by have := boundedPoly_degree (g j) (v.val j); omega)
      have hv : P *ᵥ (fun j => (v.val j).val) = 0 := v.property
      funext ik
      rw [Matrix.toLin'_apply, weightedCoefficientMatrix_mulVec, he, hv]
      rfl⟩
    left_inv := fun v => by
      apply Subtype.ext
      funext jl
      simp [weightedCoefficientPolynomial, boundedPolyOf]
    right_inv := fun v => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (p := (v.val j).val) (n := g j + 1) (by have := boundedPoly_degree (g j) (v.val j); omega)
    map_add' := fun v w => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      change Polynomial.ofFn (g j + 1) _ = _
      exact map_add (Polynomial.ofFn (g j + 1)) _ _
    map_smul' := fun c v => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      change Polynomial.ofFn (g j + 1) _ = _
      exact map_smul (Polynomial.ofFn (g j + 1)) c _ }

theorem weighted_coefficient_kernel_finrank [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (weightedCoefficientMatrix P g h))) =
      Module.finrank K (weightedPolynomialKernel P g) :=
  (weightedCoefficientKernelEquiv P g h hP).finrank_eq

theorem weighted_coefficient_injective_of_kernel_zero [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (hz : Module.finrank K (weightedPolynomialKernel P g) = 0) :
    Function.Injective (weightedCoefficientMatrix P g h).mulVec := by
  change Function.Injective (Matrix.toLin' (weightedCoefficientMatrix P g h))
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  rw [weighted_coefficient_kernel_finrank P g h hP, hz]

theorem weighted_kernel_finrank_of_coefficient_injective [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (hi : Function.Injective (weightedCoefficientMatrix P g h).mulVec) :
    Module.finrank K (weightedPolynomialKernel P g) = 0 := by
  rw [← weighted_coefficient_kernel_finrank P g h hP,
    LinearMap.ker_eq_bot.mpr hi, finrank_bot]

theorem weighted_coefficient_surjective_of_kernel_finrank
    [Fintype a] [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (hh : Module.finrank K (weightedPolynomialKernel P g) +
      (∑ i, (h i + 1)) = ∑ j, (g j + 1)) :
    Function.Surjective (weightedCoefficientMatrix P g h).mulVec := by
  change Function.Surjective (Matrix.toLin' (weightedCoefficientMatrix P g h))
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have he := (Matrix.toLin' (weightedCoefficientMatrix P g h)).finrank_range_add_finrank_ker
  rw [weighted_coefficient_kernel_finrank P g h hP] at he
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin] at he ⊢
  omega

theorem weighted_kernel_finrank_of_coefficient_surjective
    [Fintype a] [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (hs : Function.Surjective (weightedCoefficientMatrix P g h).mulVec) :
    Module.finrank K (weightedPolynomialKernel P g) =
      (∑ j, (g j + 1)) - ∑ i, (h i + 1) := by
  have hh := (Matrix.toLin' (weightedCoefficientMatrix P g h)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top,
    weighted_coefficient_kernel_finrank P g h hP] at hh
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin] at hh
  omega

end FD56
