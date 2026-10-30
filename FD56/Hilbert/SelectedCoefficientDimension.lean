/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelectedPolynomialCoefficients
import FD56.Hilbert.KernelDimension

/-! Selected coefficient equations bound the dimension of a polynomial
kernel even when the polynomial matrix has degree greater than one. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K a b c : Type*} [Field K] [Fintype b] [DecidableEq b]

theorem polynomial_kernel_finrank_le_selected_coefficient_kernel
    (P : Matrix a b K[X]) (d : ℕ) (rows : c → a × ℕ) :
    Module.finrank K (polynomialKernelAtDegree P d) ≤
      Module.finrank K (LinearMap.ker
        (Matrix.toLin' (selectedPolynomialCoefficientMatrix P d rows))) := by
  classical
  let f : polynomialKernelAtDegree P d →ₗ[K] LinearMap.ker
      (Matrix.toLin' (selectedPolynomialCoefficientMatrix P d rows)) :=
    { toFun := fun v => ⟨fun jk => (v.val jk.1).val.coeff jk.2.val, by
        have he : coefficientVectorPolynomial d (fun jk => (v.val jk.1).val.coeff jk.2.val)=
            fun j => (v.val j).val := by
          funext j
          exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
            (p:=(v.val j).val) (n:=d+1) (by have := boundedPoly_degree d (v.val j); omega)
        have hv : P *ᵥ (fun j => (v.val j).val)=0 := v.property
        funext i
        rw [Matrix.toLin'_apply,selectedPolynomialCoefficientMatrix_mulVec,he,hv]
        rfl⟩
      map_add' := by intro v w; ext jk; simp
      map_smul' := by intro t v; ext jk; simp }
  apply LinearMap.finrank_le_finrank_of_injective (f:=f)
  intro v w h
  apply Subtype.ext
  funext j
  apply Subtype.ext
  apply Polynomial.ext
  intro k
  by_cases hk : k<d+1
  · exact congrArg (fun x : LinearMap.ker
      (Matrix.toLin' (selectedPolynomialCoefficientMatrix P d rows)) =>
        x.val (j,⟨k,hk⟩)) h
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (boundedPoly_degree d (v.val j)) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (boundedPoly_degree d (w.val j)) (by omega))]

theorem polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (P : Matrix a b K[X]) (d : ℕ) (rows : c → a × ℕ) :
    Module.finrank K (polynomialKernelAtDegree P d) +
      Module.finrank K (LinearMap.range
        (Matrix.toLin' (selectedPolynomialCoefficientMatrix P d rows))) ≤
      Fintype.card b*(d+1) := by
  classical
  have h := polynomial_kernel_finrank_le_selected_coefficient_kernel P d rows
  have he := (Matrix.toLin' (selectedPolynomialCoefficientMatrix P d rows)).finrank_range_add_finrank_ker
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_prod,Fintype.card_fin] at he
  omega

end FD56
