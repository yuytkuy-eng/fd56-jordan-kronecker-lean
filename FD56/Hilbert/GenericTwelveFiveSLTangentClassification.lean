/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTwelveFiveTangentVanishing
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.LinearAlgebra.AffineKernelFrameRank
import FD56.LinearAlgebra.SelectedFrameTranspose
import FD56.LinearAlgebra.ReducedFactorKernelTest
import FD56.LinearAlgebra.MatrixFactorRelations

/-! The generic twelve-state, five-output SL pencil has seven minimal
degrees fourteen, hence seven Kronecker blocks of dimension twenty-nine.
The proof uses an actual Plucker tangent certificate and faithful
specialization of its coefficient algebra. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

theorem generic_twelve_five_sl_tangent_degrees (i₀ : Fin 12) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) i₀) (List.replicate 7 14) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin 12) (Fin 5))
  let M := genericAffineSquare K (Fin 12) (Fin 5)
  let P := genericAffineRows K (Fin 12) (Fin 5)
  let S := slEquationMatrix M P i₀
  obtain ⟨xs,hlen,hsum,hmin,_⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin 12) (m:=Fin 5) 2 (by decide) i₀ (by decide) (by decide)
  norm_num only [Fintype.card_fin,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at hlen hsum
  obtain ⟨r,B,e,hV,hlead,hperm⟩ := hmin
  have hr : r=7 := by simpa only [List.length_ofFn,hlen] using hperm.length_eq
  subst r
  have heSum : (∑ i, e i)=98 := by
    have h := hperm.sum_eq
    rw [List.sum_ofFn] at h
    omega
  let V := polynomialKernelBasisMatrix S B
  let Z := genericTwoColumnInteriorScalarGradients (K:=K) 3 2
  let A := fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 2)
  have hVinj : Function.Injective V.mulVec := polynomialKernelBasisMatrix_injective S B
  obtain ⟨C,hVC⟩ := polynomialKernelFrame_factor S B Z
    (twoColumnInteriorScalarGradients_kernel 3 2 M P i₀)
  change V*C=Z at hVC
  let select : Option (Fin 2 × Fin 3) → Fin 5 × Fin 5 :=
    fun z => (interiorTerminalRow 2 3 z 0,interiorTerminalRow 2 3 z 1)
  let φ : L[X] →+* RatFunc L := algebraMap L[X] (RatFunc L)
  have hφ : Function.Injective φ := IsFractionRing.injective L[X] (RatFunc L)
  have hCinj : Function.Injective C.transpose.mulVec := by
    apply factor_transpose_injective_of_selected_field_frame V C φ hφ select (by decide)
    rw [hVC]
    change Function.Injective (((twoColumnInteriorScalarGradients 3 2 M P).submatrix id
      (fun z => (interiorTerminalRow 2 3 z 0,interiorTerminalRow 2 3 z 1))).map φ).mulVec
    rw [twoColumnInteriorScalarGradients_selected]
    exact generic_interior_scalar_lifts_field_injective 2 3 2 φ hφ
  have hCalt := factor_columns_alternating V C hVinj
    (by
      intro t i
      rw [hVC]
      exact (generic_two_column_gradients_alternating (K:=K) 3 2 t).1 i)
    (by
      intro t i j
      rw [hVC]
      exact (generic_two_column_gradients_alternating (K:=K) 3 2 t).2 i j)
  let C₁ := C.submatrix id fiveOutputPair
  have hC₁ : Function.Injective C₁.transpose.mulVec :=
    transpose_upper_pairs_injective C hCinj hCalt.1 hCalt.2
  have hVC₁ : V*C₁=Z.submatrix id fiveOutputPair := by
    rw [←hVC]
    rfl
  have hZdegree : DegreeBound Z 20 := by
    simpa only [twoColumnInteriorWeight,Nat.reduceAdd,Nat.reduceMul,Nat.reduceDiv,Nat.reduceSub]
      using generic_two_column_scalar_gradients_degree (K:=K) 3 2
  have hVCdegree : DegreeBound (V*C₁) 20 := by
    rw [hVC₁]
    intro i j
    exact hZdegree i (fiveOutputPair j)
  have hAZ : A*(V*C₁).transpose=0 := by
    rw [hVC₁]
    funext i t
    change (fiveOutputPluckerTangent (genericTwoColumnInteriorMinors (K:=K) 3 2)*ᵥ
      (fun j => genericTwoColumnInteriorScalarGradients (K:=K) 3 2 t (fiveOutputPair j))) i=0
    rw [fiveOutputPluckerTangent_mulVec _
      (fun a b => genericTwoColumnInteriorScalarGradients (K:=K) 3 2 t (a,b))]
    exact generic_two_column_gradient_plucker_relation (K:=K) 3 2 t
      (fiveOutputQuad i 0) (fiveOutputQuad i 1) (fiveOutputQuad i 2) (fiveOutputQuad i 3)
  have hAC : A*C₁.transpose=0 := factor_transpose_kernel_of_product V C₁ A hVinj hAZ
  have he : ∀ i, e i=14 := by
    apply reduced_factor_degrees_eq_of_kernel_vanishing_and_sum V C₁ e 20 5
      hV hlead hC₁ hVCdegree A hAC
      (generic_twelve_five_tangent_bounded_kernel_zero (K:=K))
    simpa only [Fintype.card_fin,Nat.reduceSub,Nat.reduceMul] using heSum
  refine ⟨7,B,e,hV,hlead,?_⟩
  have hef : e=fun _ => 14 := funext he
  rw [hef,List.ofFn_const]

theorem generic_twelve_five_sl_tangent_kronecker (i₀ : Fin 12) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) i₀) (List.replicate 7 14) := by
  apply slKirillovMatrix_kronecker _ _ i₀ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_twelve_five_sl_tangent_degrees i₀)
  norm_num [slChartInput_card,nat_list_affine_sum,SLInput]

theorem generic_twelve_five_sl_tangent_classification (i₀ : Fin 12) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) i₀) (List.replicate 7 14) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 12) (Fin 5))
      (genericAffineRows K (Fin 12) (Fin 5)) i₀) (List.replicate 7 14) :=
  ⟨generic_twelve_five_sl_tangent_degrees i₀,generic_twelve_five_sl_tangent_kronecker i₀⟩

end FD56
