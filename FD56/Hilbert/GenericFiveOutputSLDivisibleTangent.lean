/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericFiveOutputSLTangentCriterion
import FD56.Hilbert.GenericTwoColumnFullSpecialization
import FD56.LinearAlgebra.ReducedFactorKernelTest
import FD56.LinearAlgebra.PowerSubstitutionKernel
import FD56.Hilbert.SevenSevenTangentWitness
import FD56.LinearAlgebra.FiveOutputTangentTransfer
import FD56.LinearAlgebra.FullSelectedPolynomialCoefficients
import FD56.Arithmetic.FiveOutputTangentResidues

/-! A verified equal-degree tangent witness, power substitution, and faithful
specialization determine an infinite family of generic five-output SL
pencils. Their seven Kronecker indices are equal. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private abbrev DivisibleFiveOutputField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (5*q+2)) (Fin 5))

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

private theorem divisible_faithful_realization (q h : ℕ) (hq : 0<q)
    (hweight : twoColumnInteriorWeight 3 q=14*h) :
    ∃ u v : Fin 5 → (DivisibleFiveOutputField (K:=K) q)[X],
      (∀ i, (u i).natDegree≤7*h) ∧ (∀ i, (v i).natDegree≤7*h) ∧
      genericTwoColumnInteriorMinors (K:=K) 3 q=twoColumnWedge u v ∧
      Function.Injective (twoColumnMinorSpecialization (7*h) (7*h)
        (twoColumnCoefficientEvaluation (K:=K) (7*h) (7*h) u v)) := by
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,hF,hfaithful⟩ :=
    generic_two_column_full_specialization_faithful (K:=K) 3 q hq
  have habsum : a+b=14*h := by
    unfold twoColumnInteriorWeight at hweight
    norm_num only [Nat.reduceAdd] at hweight hsum
    omega
  have ha : a=7*h := by omega
  have hb : b=7*h := by omega
  subst a
  subst b
  exact ⟨u,v,hu,hv,hF,hfaithful⟩

private theorem divisible_degrees_of_vanishing (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : twoColumnInteriorWeight 3 q=14*h) (i₀ : Fin (5*q+2))
    (hzero : ∀ z : Fin 10 → (DivisibleFiveOutputField (K:=K) q)[X],
      fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q)*ᵥz=0 →
      (∀ j, (z j).natDegree≤4*h-1) → z=0) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) := by
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_five_output_sl_tangent_factor (K:=K) q hq i₀
  have hbudget : (∑ i, e i)=Fintype.card (Fin 7)*
      ((twoColumnInteriorWeight 3 q-1)-(4*h-1)-1) := by
    rw [hweight] at hsum ⊢
    simp only [Fintype.card_fin]
    omega
  have he := reduced_factor_degrees_eq_of_kernel_vanishing_and_sum
    (polynomialKernelBasisMatrix _ B) C e (twoColumnInteriorWeight 3 q-1) (4*h-1)
    hV hlead hC hVC _ hAC hzero hbudget
  have hef : e=fun _ => 10*h-1 := by
    funext i
    have hi := he i
    rw [hweight] at hi
    omega
  refine ⟨7,B,e,hV,hlead,?_⟩
  rw [hef,List.ofFn_const]

theorem generic_five_output_divisible_tangent_bounded_kernel_zero
    (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : twoColumnInteriorWeight 3 q=14*h)
    (z : Fin 10 → (DivisibleFiveOutputField (K:=K) q)[X])
    (hz : fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 q)*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤4*h-1) : z=0 := by
  obtain ⟨u,v,hu,hv,hF,hfaithful⟩ := divisible_faithful_realization (K:=K) q h hq hweight
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
  rw [hF] at hz
  exact bounded_kernel_zero_of_selected_coefficient_injective _ (4*h-1) rows hactual z hz hdeg

theorem generic_five_output_sl_divisible_tangent_degrees (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : twoColumnInteriorWeight 3 q=14*h) (i₀ : Fin (5*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) :=
  divisible_degrees_of_vanishing q h hq hh hweight i₀
    (generic_five_output_divisible_tangent_bounded_kernel_zero q h hq hh hweight)

theorem generic_five_output_sl_divisible_tangent_classification (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : twoColumnInteriorWeight 3 q=14*h) (i₀ : Fin (5*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) := by
  have hmin := generic_five_output_sl_divisible_tangent_degrees (K:=K) q h hq hh hweight i₀
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (5*q+2)) (m:=Fin 5) q hq i₀
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  have hp : xs.Perm (List.replicate 7 (10*h-1)) := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

theorem generic_five_output_sl_residue_tangent_classification (q : ℕ) (hq : 0<q)
    (hres : q%28=16 ∨ q%28=20 ∨ q%28=23 ∨ q%28=27) (i₀ : Fin (5*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (List.replicate 7 (10*(twoColumnInteriorWeight 3 q/14)-1)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (List.replicate 7 (10*(twoColumnInteriorWeight 3 q/14)-1)) := by
  have hW : 2*twoColumnInteriorWeight 3 q=5*q^2+9*q+4 := by
    obtain ⟨h,hh⟩ := Nat.even_mul_succ_self q
    have hn : 5*q*(q+1)+4*(q+1)=2*(5*h+2*(q+1)) := by nlinarith
    unfold twoColumnInteriorWeight
    norm_num only [Nat.reduceAdd]
    have hd : (5*q*(q+1)+4*(q+1))/2=5*h+2*(q+1) := by omega
    rw [hd]
    nlinarith
  obtain ⟨h,hh,hweight⟩ := five_output_tangent_positive_multiplier q (twoColumnInteriorWeight 3 q) hW hres
  have hdiv : twoColumnInteriorWeight 3 q/14=h := by omega
  rw [hdiv]
  exact generic_five_output_sl_divisible_tangent_classification q h hq hh hweight i₀

end FD56
