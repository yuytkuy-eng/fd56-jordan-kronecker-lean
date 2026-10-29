/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericFiveOutputCorankTwoSLTangentFactor
import FD56.Hilbert.PoweredSevenSevenTangent
import FD56.LinearAlgebra.ReducedFactorKernelTest
import FD56.Arithmetic.FiveOutputCorankTwoTangentResidues

/-! An infinite family of actual generic five-output, corank-two SL pencils
has seven equal Kronecker indices, proved by a faithful tangent certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private abbrev CorankTwoDivisibleField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5))

private theorem divisible_faithful_realization (q h : ℕ) (hq : 0<q)
    (hweight : interiorFullWeight 3 2 q=14*h) :
    ∃ u v : Fin 5 → (CorankTwoDivisibleField (K:=K) q)[X],
      (∀ i, (u i).natDegree≤7*h) ∧ (∀ i, (v i).natDegree≤7*h) ∧
      genericFiveOutputCorankTwoMinors (K:=K) q=twoColumnWedge u v ∧
      Function.Injective (twoColumnMinorSpecialization (7*h) (7*h)
        (twoColumnCoefficientEvaluation (K:=K) (7*h) (7*h) u v)) := by
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,hF,hfaithful⟩ :=
    generic_five_output_corank_two_full_specialization_faithful (K:=K) q hq
  have ha : a=7*h := by omega
  have hb : b=7*h := by omega
  subst a
  subst b
  exact ⟨u,v,hu,hv,hF,hfaithful⟩

private theorem divisible_degrees_of_vanishing (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : interiorFullWeight 3 2 q=14*h) (i₀ : Fin (5*q+3))
    (hzero : ∀ z : Fin 10 → (CorankTwoDivisibleField (K:=K) q)[X],
      fiveOutputPluckerTangent (genericFiveOutputCorankTwoMinors (K:=K) q)*ᵥz=0 →
      (∀ j, (z j).natDegree≤4*h-1) → z=0) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) := by
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_five_output_corank_two_sl_tangent_factor (K:=K) q hq i₀
  have hbudget : (∑ i, e i)=Fintype.card (Fin 7)*
      ((interiorFullWeight 3 2 q-1)-(4*h-1)-1) := by
    rw [hweight] at hsum ⊢
    simp only [Fintype.card_fin]
    omega
  have he := reduced_factor_degrees_eq_of_kernel_vanishing_and_sum
    (polynomialKernelBasisMatrix _ B) C e (interiorFullWeight 3 2 q-1) (4*h-1)
    hV hlead hC hVC _ hAC hzero hbudget
  have hef : e=fun _ => 10*h-1 := by
    funext i
    have hi := he i
    rw [hweight] at hi
    omega
  refine ⟨7,B,e,hV,hlead,?_⟩
  rw [hef,List.ofFn_const]

theorem generic_five_output_corank_two_divisible_tangent_bounded_kernel_zero
    (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : interiorFullWeight 3 2 q=14*h)
    (z : Fin 10 → (CorankTwoDivisibleField (K:=K) q)[X])
    (hz : fiveOutputPluckerTangent (genericFiveOutputCorankTwoMinors (K:=K) q)*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤4*h-1) : z=0 := by
  obtain ⟨u,v,hu,hv,hF,hfaithful⟩ := divisible_faithful_realization (K:=K) q h hq hweight
  rw [hF] at hz
  exact five_output_equal_powered_tangent_bounded_kernel_zero
    (K:=K) h hh u v hu hv hfaithful z hz hdeg

theorem generic_five_output_corank_two_sl_divisible_tangent_degrees (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : interiorFullWeight 3 2 q=14*h) (i₀ : Fin (5*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) :=
  divisible_degrees_of_vanishing q h hq hh hweight i₀
    (generic_five_output_corank_two_divisible_tangent_bounded_kernel_zero q h hq hh hweight)

theorem generic_five_output_corank_two_sl_divisible_tangent_classification (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : interiorFullWeight 3 2 q=14*h) (i₀ : Fin (5*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀) (List.replicate 7 (10*h-1)) := by
  have hmin := generic_five_output_corank_two_sl_divisible_tangent_degrees (K:=K) q h hq hh hweight i₀
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (5*q+3)) (m:=Fin 5) q hq i₀
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
  have hp : xs.Perm (List.replicate 7 (10*h-1)) := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

theorem generic_five_output_corank_two_sl_residue_tangent_classification (q : ℕ) (hq : 0<q)
    (hres : q%28=3 ∨ q%28=6 ∨ q%28=10 ∨ q%28=27) (i₀ : Fin (5*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (List.replicate 7 (10*(interiorFullWeight 3 2 q/14)-1)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (List.replicate 7 (10*(interiorFullWeight 3 2 q/14)-1)) := by
  have hW := five_output_corank_two_weight_twice q
  obtain ⟨h,hh,hweight⟩ := five_output_corank_two_tangent_positive_multiplier q (interiorFullWeight 3 2 q) hW hres
  have hdiv : interiorFullWeight 3 2 q/14=h := by omega
  rw [hdiv]
  exact generic_five_output_corank_two_sl_divisible_tangent_classification q h hq hh hweight i₀

end FD56
