/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDerivationImage

/-! Sharp differential rank makes actual coefficient variations exhaust the
bounded variations of a polynomial Plucker presentation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L m r ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype m] [Fintype r] [DecidableEq r]

def signedPluckerProjection (row : ι → r → m) (sign : ι → K) :
    ((r → m) → L[X]) →ₗ[L] (ι → L[X]) where
  toFun z i := algebraMap K L (sign i) • z (row i)
  map_add' := by intro x y; funext i; exact smul_add _ _ _
  map_smul' := by
    intro a x
    funext i
    exact smul_comm (algebraMap K L (sign i)) a (x (row i))

omit [Fintype m] in
private theorem actual_derivation_range_le (row : ι → r → m) (sign : ι → K)
    (c : L) (G : Matrix m r L[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j) :
    LinearMap.range (polynomialDerivationImageMap (K:=K)
      (fun i => C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i))) ≤
      LinearMap.range ((signedPluckerProjection row sign).comp
        (weightedPluckerDifferential c G d)) := by
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

theorem polynomial_derivation_range_eq_weighted_plucker_range
    (row : ι → r → m) (sign : ι → K)
    (c : L) (G : Matrix m r L[X]) (d : r → ℕ)
    (hdegree : ∀ i j, (G i j).natDegree ≤ d j)
    (hG : Function.Injective G.mulVec)
    (hcard : Fintype.card r ≤ Fintype.card m)
    (hlower : Fintype.card m*(∑ j, d j)+
      (Fintype.card m-Fintype.card r)*Fintype.card r+1 ≤
      Module.finrank L (LinearMap.range (polynomialDerivationImageMap (K:=K)
        (fun i => C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i))))) :
    LinearMap.range (polynomialDerivationImageMap (K:=K)
      (fun i => C (algebraMap K L (sign i))*C c*pluckerMinorVector G (row i))) =
      LinearMap.range ((signedPluckerProjection row sign).comp
        (weightedPluckerDifferential c G d)) := by
  apply Submodule.eq_of_le_of_finrank_le (actual_derivation_range_le row sign c G d hdegree)
  have hupper := weightedPluckerDifferential_postcomp_finrank_range_bound
    (signedPluckerProjection row sign) c G d hdegree hG
  have hendo := degreeEndomorphismDimension_ge_card_sq d
  have hsum : (∑ j, (d j+1))=(∑ j, d j)+Fintype.card r := by
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
  rw [hsum] at hupper
  have hc : Fintype.card m=Fintype.card r+(Fintype.card m-Fintype.card r) := by omega
  nlinarith

end FD56
