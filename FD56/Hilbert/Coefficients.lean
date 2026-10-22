/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CoefficientMatrix
import FD56.Hilbert.KernelDimension

/-! Coefficient vectors and bounded polynomial kernels have the same dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

def reindexKernelEquiv {c e : Type*} [Fintype e]
    (P : Matrix a b K[X]) (er : c ≃ a) (ec : e ≃ b) (d : ℕ) :
    polynomialKernelAtDegree (P.submatrix er ec) d ≃ₗ[K]
      polynomialKernelAtDegree P d where
  toFun v := ⟨fun j => v.val (ec.symm j), by
    have hv : P.submatrix er ec *ᵥ (fun j => (v.val j).val) = 0 := v.property
    rw [Matrix.submatrix_mulVec_equiv] at hv
    funext i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using
      congrFun hv (er.symm i)⟩
  invFun v := ⟨fun j => v.val (ec j), by
    change P.submatrix er ec *ᵥ (fun j => (v.val (ec j)).val) = 0
    rw [Matrix.submatrix_mulVec_equiv]
    have hv : P *ᵥ (fun j => (v.val j).val) = 0 := v.property
    simp only [Function.comp_def, Equiv.apply_symm_apply, hv, Pi.zero_apply]
    rfl⟩
  left_inv v := by apply Subtype.ext; funext j; simp
  right_inv v := by apply Subtype.ext; funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq b] in
theorem reindex_kernel_hilbert {c e : Type*} [Fintype e]
    (P : Matrix a b K[X]) (er : c ≃ a) (ec : e ≃ b) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (P.submatrix er ec) d) =
      Module.finrank K (polynomialKernelAtDegree P d) :=
  (reindexKernelEquiv P er ec d).finrank_eq

def coefficientKernelEquiv (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1) :
    LinearMap.ker (Matrix.toLin' (polynomialCoefficientMatrix P d)) ≃ₗ[K]
      polynomialKernelAtDegree P d := by
  classical
  exact {
    toFun := fun v => ⟨fun j => boundedPolyOf (coefficientVectorPolynomial d v.val j)
      (coefficientVectorPolynomial_degree d v.val j),
        coefficient_matrix_kernel_zero P d hP v.val v.property⟩
    invFun := fun v => ⟨fun jl => (v.val jl.1).val.coeff jl.2.val, by
      have he : coefficientVectorPolynomial d
          (fun jl => (v.val jl.1).val.coeff jl.2.val) = fun j => (v.val j).val := by
        funext j
        exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (p := (v.val j).val) (n := d + 1)
          (by have := boundedPoly_degree d (v.val j); omega)
      have hv : P *ᵥ (fun j => (v.val j).val) = 0 := v.property
      funext ik
      rw [Matrix.toLin'_apply, polynomialCoefficientMatrix_mulVec, he, hv]
      rfl⟩
    left_inv := fun v => by
      apply Subtype.ext
      funext jl
      simp [coefficientVectorPolynomial, boundedPolyOf]
    right_inv := fun v => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (p := (v.val j).val) (n := d + 1)
        (by have := boundedPoly_degree d (v.val j); omega)
    map_add' := fun v w => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      change Polynomial.ofFn (d + 1) _ = _
      exact map_add (Polynomial.ofFn (d + 1)) _ _
    map_smul' := fun c v => by
      apply Subtype.ext
      funext j
      apply Subtype.ext
      change Polynomial.ofFn (d + 1) _ = _
      exact map_smul (Polynomial.ofFn (d + 1)) c _ }

theorem coefficient_kernel_finrank (P : Matrix a b K[X]) (d : ℕ)
    (hP : DegreeBound P 1) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (polynomialCoefficientMatrix P d))) =
      Module.finrank K (polynomialKernelAtDegree P d) :=
  (coefficientKernelEquiv P d hP).finrank_eq

theorem polynomial_kernel_hilbert_of_coefficient_surjective [Fintype a]
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hs : Function.Surjective (polynomialCoefficientMatrix P d).mulVec) :
    Module.finrank K (polynomialKernelAtDegree P d) =
      Fintype.card b * (d + 1) - Fintype.card a * (d + 2) := by
  have hh := (Matrix.toLin' (polynomialCoefficientMatrix P d)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, coefficient_kernel_finrank P d hP] at hh
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at hh
  omega

theorem coefficient_surjective_of_kernel_finrank [Fintype a]
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hh : Module.finrank K (polynomialKernelAtDegree P d) +
      Fintype.card a * (d + 2) = Fintype.card b * (d + 1)) :
    Function.Surjective (polynomialCoefficientMatrix P d).mulVec := by
  change Function.Surjective (Matrix.toLin' (polynomialCoefficientMatrix P d))
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  have he := (Matrix.toLin' (polynomialCoefficientMatrix P d)).finrank_range_add_finrank_ker
  rw [coefficient_kernel_finrank P d hP] at he
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at he ⊢
  omega

theorem coefficient_injective_of_kernel_finrank_zero
    (P : Matrix a b K[X]) (d : ℕ) (hP : DegreeBound P 1)
    (hh : Module.finrank K (polynomialKernelAtDegree P d) = 0) :
    Function.Injective (polynomialCoefficientMatrix P d).mulVec := by
  change Function.Injective (Matrix.toLin' (polynomialCoefficientMatrix P d))
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  rw [coefficient_kernel_finrank P d hP, hh]

omit [DecidableEq b] in
theorem polynomial_kernel_hilbert_of_coefficient_injective
    (P : Matrix a b K[X]) (d : ℕ)
    (hi : Function.Injective (polynomialCoefficientMatrix P d).mulVec) :
    Module.finrank K (polynomialKernelAtDegree P d) = 0 := by
  have hz : polynomialKernelAtDegree P d = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have hh := bounded_kernel_zero_of_coefficient_matrix_injective P d hi _ hv
      (fun j => boundedPoly_degree d (v j))
    funext j
    exact Subtype.ext (congrFun hh j)
  rw [hz, finrank_bot]

end FD56
