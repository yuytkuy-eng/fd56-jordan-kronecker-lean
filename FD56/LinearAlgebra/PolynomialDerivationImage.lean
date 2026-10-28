/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialCoefficientDerivation
import FD56.LinearAlgebra.WeightedPluckerDifferential

/-! Coefficientwise variation of a polynomial family is linear in the
derivation of its coefficient field. -/

noncomputable section
namespace FD56
open Polynomial
open scoped BigOperators
variable {K L j : Type*} [Field K] [Field L] [Algebra K L]

def polynomialDerivationImageMap (p : j → L[X]) :
    Derivation K L L →ₗ[L] (j → L[X]) where
  toFun D i := polynomialCoefficientDerivation D (p i)
  map_add' D E := by
    funext i
    apply Polynomial.ext
    intro k
    simp [polynomialCoefficientDerivation_coeff]
  map_smul' c D := by
    funext i
    apply Polynomial.ext
    intro k
    simp [polynomialCoefficientDerivation_coeff]

theorem polynomialDerivationImageMap_coeff (p : j → L[X]) (D : Derivation K L L)
    (i : j) (k : ℕ) :
    (polynomialDerivationImageMap p D i).coeff k=D ((p i).coeff k) := rfl

theorem polynomial_derivation_plucker_rank_bound {m r : Type*}
    [Fintype m] [Fintype r] [DecidableEq r]
    (c : L) (G : Matrix m r L[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j)
    (hG : Function.Injective G.mulVec) :
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap
      (fun row => C c*pluckerMinorVector G row) :
        Derivation K L L →ₗ[L] ((r → m) → L[X])))+
      degreeEndomorphismDimension d ≤ 1+Fintype.card m*(∑ j, (d j+1)) := by
  let T := weightedPluckerDifferential c G d
  have hi : LinearMap.range (polynomialDerivationImageMap
      (fun row => C c*pluckerMinorVector G row) :
        Derivation K L L →ₗ[L] ((r → m) → L[X])) ≤ LinearMap.range T := by
    rintro y ⟨D,rfl⟩
    let E : ∀ i j, BoundedPoly L (d j) := fun i j =>
      boundedPolyOf (polynomialCoefficientDerivation D (G i j))
        (polynomialCoefficientDerivation_degree_bound D _ _ (hdegree i j))
    refine ⟨(D c,E),?_⟩
    have h := pluckerScalarMinorVector_derivation (polynomialCoefficientDerivation D) (C c) G
    rw [polynomialCoefficientDerivation_C] at h
    exact h.symm
  have hb := weightedPluckerDifferential_finrank_range_bound c G d hdegree hG
  have hr := Submodule.finrank_mono hi
  exact (Nat.add_le_add_right hr _).trans hb

theorem polynomial_derivation_signed_selected_plucker_rank_bound {m r ι : Type*}
    [Fintype m] [Fintype r] [DecidableEq r]
    (row : ι → r → m) (sign : ι → K)
    (c : L) (G : Matrix m r L[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j)
    (hG : Function.Injective G.mulVec) :
    Module.finrank L (LinearMap.range (polynomialDerivationImageMap
      (fun i => C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i)) :
        Derivation K L L →ₗ[L] (ι → L[X])))+
      degreeEndomorphismDimension d ≤ 1+Fintype.card m*(∑ j, (d j+1)) := by
  let T : ((r → m) → L[X]) →ₗ[L] (ι → L[X]) :=
    { toFun := fun z i => algebraMap K L (sign i) • z (row i)
      map_add' := by intro x y; funext i; exact smul_add _ _ _
      map_smul' := by
        intro a x
        funext i
        exact smul_comm (algebraMap K L (sign i)) a (x (row i)) }
  have hi : LinearMap.range (polynomialDerivationImageMap
      (fun i => C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i)) :
        Derivation K L L →ₗ[L] (ι → L[X])) ≤
      LinearMap.range (T.comp (weightedPluckerDifferential c G d)) := by
    rintro y ⟨D,rfl⟩
    let E : ∀ i j, BoundedPoly L (d j) := fun i j =>
      boundedPolyOf (polynomialCoefficientDerivation D (G i j))
        (polynomialCoefficientDerivation_degree_bound D _ _ (hdegree i j))
    refine ⟨(D c,E),?_⟩
    have h := pluckerScalarMinorVector_derivation (polynomialCoefficientDerivation D) (C c) G
    rw [polynomialCoefficientDerivation_C] at h
    funext i
    change algebraMap K L (sign i) •
        (pluckerScalarDifferential (C c) G (C (D c),G.map (polynomialCoefficientDerivation D)))
          (row i)=polynomialCoefficientDerivation D
        (C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i))
    rw [← h,mul_assoc,Derivation.leibniz,polynomialCoefficientDerivation_C,
      Derivation.map_algebraMap,map_zero,smul_zero,add_zero]
    exact Polynomial.smul_eq_C_mul (algebraMap K L (sign i))
  have hb := weightedPluckerDifferential_postcomp_finrank_range_bound T c G d hdegree hG
  have hr := Submodule.finrank_mono hi
  exact (Nat.add_le_add_right hr _).trans hb

end FD56
