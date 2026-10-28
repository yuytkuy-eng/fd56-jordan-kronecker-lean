/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericFourOutputCoprimeChart
import FD56.Hilbert.PluckerChartBalance
import FD56.Hilbert.PluckerConstantMinimalDegrees
import FD56.Hilbert.FourOutputSLBalancedTransfer

/-! The actual generic SL pencil with four outputs and 4q+2 states has five
balanced Kronecker indices at every positive depth in characteristic zero.
The proof transfers an explicit balanced Plucker certificate through a
base-field chart and the exact complementary-degree identity. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 200000

variable {K : Type*} [Field K] [CharZero K]

private theorem four_output_weight_lower (q : ℕ) (hq : 0<q) : 5≤2*(q+1)^2 := by
  nlinarith

theorem generic_four_output_polar_minimal_degrees (q : ℕ) (hq : 0<q) :
    HasMinimalKernelDegrees
      (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q))
      (balancedDegreeList (2*(q+1)^2) 5) := by
  obtain ⟨Q,S,hQS,hSQ,hchart⟩ := generic_four_output_coprime_chart (K:=K) q hq
  let F := pluckerConstantOutputChange Q (genericFourOutputInteriorMinors (K:=K) q)
  change (∀ i, (F i).natDegree≤2*(q+1)^2) ∧ (F 0).natDegree=2*(q+1)^2 ∧
    IsCoprime (F 0) (F 1) ∧ pluckerQuadric F=0 ∧ _ at hchart
  obtain ⟨hF,hfirst,hcop,hquad,hrank⟩ := hchart
  have hW : 5≤2*(q+1)^2 := four_output_weight_lower q hq
  have hF0 : F 0≠0 := by
    intro hz
    rw [hz,Polynomial.natDegree_zero] at hfirst
    exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<5) hW)) hfirst.symm
  have hrank' : 4*(2*(q+1)^2+1)+1≤
      Module.finrank (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))
        (LinearMap.range (polynomialDerivationImageMap (K:=K) F)) := by
    have heq : 4*(2*(q+1)^2+1)+1=4*(2*(q+1)^2)+5 := by ring
    rw [heq]
    exact hrank
  have hmin := pluckerChart_balanced_minimal_degrees_of_derivation_rank (K:=K)
    (2*(q+1)^2) hW F hF hF0 hfirst hcop hquad hrank'
  have hordinary := (pluckerConstantOutputChange_minimal_degrees_iff Q S hQS hSQ
    (genericFourOutputInteriorMinors (K:=K) q) (balancedDegreeList (2*(q+1)^2) 5)).mp hmin
  exact (pluckerPolarRow_minimal_degrees_iff _ _).mpr hordinary

theorem generic_four_output_interior_sl_minimal_degrees
    (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀)
      (balancedDegreeList (8*q^2+16*q+3) 5) :=
  generic_four_output_sl_minimal_degrees_of_balanced_polar q hq i₀
    (generic_four_output_polar_minimal_degrees q hq)

theorem generic_four_output_interior_sl_kronecker
    (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2)) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
      (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀)
      (balancedDegreeList (8*q^2+16*q+3) 5) :=
  generic_four_output_sl_kronecker_of_balanced_polar q hq i₀
    (generic_four_output_polar_minimal_degrees q hq)

end FD56
