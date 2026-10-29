/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PowerSubstitutionKernel
import FD56.Hilbert.SevenSevenTangentWitness
import FD56.LinearAlgebra.FiveOutputTangentTransfer
import FD56.LinearAlgebra.FullSelectedPolynomialCoefficients

/-! Power substitution of the verified degree-seven witness proves a bounded
kernel test for every faithful equal-degree five-output Plucker realization. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private def poweredSevenU (h : ℕ) : Fin 5 → K[X] :=
  fun i => Polynomial.expand K h (sevenSevenTangentU i)

private def poweredSevenV (h : ℕ) : Fin 5 → K[X] :=
  fun i => Polynomial.expand K h (sevenSevenTangentV i)

private theorem poweredSevenU_degree (h : ℕ) (i : Fin 5) :
    (poweredSevenU (K:=K) h i).natDegree≤7*h := by
  rw [poweredSevenU,Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right h (sevenSevenTangentU_degree i)

private theorem poweredSevenV_degree (h : ℕ) (i : Fin 5) :
    (poweredSevenV (K:=K) h i).natDegree≤7*h := by
  rw [poweredSevenV,Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right h (sevenSevenTangentV_degree i)

private theorem wedge_tangent_expand (h : ℕ) (u v : Fin 5 → K[X]) :
    fiveOutputPluckerTangent (twoColumnWedge
      (fun i => Polynomial.expand K h (u i)) (fun i => Polynomial.expand K h (v i)))=
      (fiveOutputPluckerTangent (twoColumnWedge u v)).map (Polynomial.expand K h) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveOutputPluckerTangent,twoColumnWedge,map_sub,map_mul]

private theorem poweredSeven_kernel_zero (h : ℕ) (hh : 0<h)
    (z : Fin 10 → K[X])
    (hz : fiveOutputPluckerTangent (twoColumnWedge
      (poweredSevenU (K:=K) h) (poweredSevenV (K:=K) h))*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤4*h-1) : z=0 := by
  apply expanded_matrix_bounded_kernel_zero (sevenSevenTangentWitness (R:=K)) 3 h hh
    sevenSevenTangent_bounded_kernel_zero_charZero z
  · change fiveOutputPluckerTangent (twoColumnWedge
      (fun i => Polynomial.expand K h (sevenSevenTangentU i))
      (fun i => Polynomial.expand K h (sevenSevenTangentV i)))*ᵥz=0 at hz
    rw [wedge_tangent_expand] at hz
    exact hz
  · simpa only [show h*(3+1)=4*h by omega] using hdeg

private theorem wedge_tangent_degree (a b : ℕ) (u v : Fin 5 → K[X])
    (hu : ∀ i, (u i).natDegree≤a) (hv : ∀ i, (v i).natDegree≤b) :
    DegreeBound (fiveOutputPluckerTangent (twoColumnWedge u v)) (a+b) := by
  have hF (i j : Fin 5) : (twoColumnWedge u v i j).natDegree≤a+b := by
    change (u i*v j-u j*v i).natDegree≤a+b
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hu i) (hv j))
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hu j) (hv i))
  intro i j
  fin_cases i <;> fin_cases j <;> simp [fiveOutputPluckerTangent,hF]

theorem five_output_equal_powered_tangent_bounded_kernel_zero
    {L : Type*} [Field L] [Algebra K L]
    (h : ℕ) (hh : 0<h) (u v : Fin 5 → L[X])
    (hu : ∀ i, (u i).natDegree≤7*h) (hv : ∀ i, (v i).natDegree≤7*h)
    (hfaithful : Function.Injective (twoColumnMinorSpecialization (7*h) (7*h)
      (twoColumnCoefficientEvaluation (K:=K) (7*h) (7*h) u v)))
    (z : Fin 10 → L[X])
    (hz : fiveOutputPluckerTangent (twoColumnWedge u v)*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤4*h-1) : z=0 := by
  let rows : Fin 5 × Fin (14*h+(4*h-1)+1) → Fin 5 × ℕ := fun ik => (ik.1,ik.2.val)
  have hwitness : Function.Injective (selectedPolynomialCoefficientMatrix
      (fiveOutputPluckerTangent (twoColumnWedge (poweredSevenU (K:=K) h) (poweredSevenV (K:=K) h)))
      (4*h-1) rows).mulVec := by
    apply full_selected_coefficient_injective_of_bounded_kernel_zero _ (14*h) (4*h-1)
    · have hdegree := wedge_tangent_degree (K:=K) (7*h) (7*h)
        (poweredSevenU h) (poweredSevenV h) (poweredSevenU_degree h) (poweredSevenV_degree h)
      simpa only [show 7*h+7*h=14*h by omega] using hdegree
    · exact poweredSeven_kernel_zero h hh
  have hactual := five_output_tangent_coefficients_injective_of_faithful
    (K:=K) (7*h) (7*h) (4*h-1) rows u v hu hv hfaithful
    (poweredSevenU h) (poweredSevenV h) (poweredSevenU_degree h) (poweredSevenV_degree h) hwitness
  exact bounded_kernel_zero_of_selected_coefficient_injective _ (4*h-1) rows hactual z hz hdeg

end FD56
