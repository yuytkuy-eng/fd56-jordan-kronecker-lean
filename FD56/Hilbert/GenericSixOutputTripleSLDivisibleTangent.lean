/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailWitness
import FD56.Hilbert.GenericSixOutputTripleTangentTransfer
import FD56.Hilbert.GenericSixOutputTripleSLTangentCriterion
import FD56.LinearAlgebra.SixOutputTripleTangentFunctor
import FD56.LinearAlgebra.PowerSubstitutionKernel
import FD56.LinearAlgebra.ReducedFactorKernelTest

/-! Power substitution determines the six-output middle-remainder family when
its equal column degree is divisible by five. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private def poweredFiveFrame (t : ℕ) : Matrix (Fin 6) (Fin 3) K[X] :=
  (sixOutputThreeColumnTailFrame (R:=K)).map (Polynomial.expand K t)

omit [CharZero K] in
private theorem poweredFiveFrame_degree (t : ℕ) (i : Fin 6) (j : Fin 3) :
    (poweredFiveFrame (K:=K) t i j).natDegree≤5*t := by
  rw [poweredFiveFrame,Matrix.map_apply,Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right t (sixOutputThreeColumnTailFrame_degree i j)

private theorem poweredFiveFrame_kernel_zero (t : ℕ) (ht : 0<t)
    (z : Fin 20 → K[X])
    (hz : sixOutputTriplePluckerTangent
      (sixOutputTriplePluckerMinors (poweredFiveFrame (K:=K) t))*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤6*t-1) : z=0 := by
  apply expanded_matrix_bounded_kernel_zero (sixOutputThreeColumnTailWitness (R:=K))
    5 t ht sixOutputThreeColumnTail_bounded_kernel_zero_charZero z
  · have he : (sixOutputThreeColumnTailWitness (R:=K)).map (Polynomial.expand K t)=
        sixOutputTriplePluckerTangent
          (sixOutputTriplePluckerMinors (poweredFiveFrame (K:=K) t)) :=
      sixOutputTripleTangent_frame_map (Polynomial.expand K t).toRingHom _
    rw [he]
    exact hz
  · simpa only [show t*(5+1)=6*t by omega] using hdeg

private theorem kernel_finrank_zero {F : Type*} [Field F]
    (P : Matrix (Fin 20) (Fin 20) F[X]) (d : ℕ)
    (hz : ∀ z : Fin 20 → F[X], P*ᵥz=0 → (∀ j, (z j).natDegree≤d) → z=0) :
    Module.finrank F (polynomialKernelAtDegree P d)=0 := by
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z h
  have he := hz (fun i => (z i).val) h (fun i => boundedPoly_degree d (z i))
  funext i
  exact Subtype.ext (congrFun he i)

private theorem kernel_zero_of_finrank_zero {F : Type*} [Field F]
    (P : Matrix (Fin 20) (Fin 20) F[X]) (d : ℕ)
    (hdim : Module.finrank F (polynomialKernelAtDegree P d)=0)
    (z : Fin 20 → F[X]) (hz : P*ᵥz=0) (hdeg : ∀ j, (z j).natDegree≤d) : z=0 := by
  let w : Fin 20 → BoundedPoly F d := fun j => boundedPolyOf (z j) (hdeg j)
  have hw : w∈polynomialKernelAtDegree P d := hz
  have hb : polynomialKernelAtDegree P d=⊥ := Submodule.finrank_eq_zero.mp hdim
  rw [hb,Submodule.mem_bot] at hw
  funext j
  exact congrArg Subtype.val (congrFun hw j)

private theorem balanced_uniform (t : ℕ) (ht : 0<t) :
    balancedDegreeList (10*(15*t-1)-4*(15*t)) 10=List.replicate 10 (9*t-1) := by
  have he : 10*(15*t-1)-4*(15*t)=10*(9*t-1) := by omega
  rw [he]
  simp [balancedDegreeList]

omit [CharZero K] in
private theorem canonical_of_minimal (q : ℕ) (hq : 0<q)
    (i₀ : Fin (6*q+3)) (ys : List ℕ)
    (hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀) ys) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀) ys := by
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin (6*q+3)) (m:=Fin 6) q hq i₀
    (by simp only [Fintype.card_fin]; omega)
    (by simp only [Fintype.card_fin]; omega)
  have hp : xs.Perm ys := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ ys).mp hmin d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

theorem generic_six_output_triple_sl_divisible_tangent_classification
    (q t : ℕ) (hq : 0<q) (ht : 0<t) (hdegree : (q+1)^2=5*t) (i₀ : Fin (6*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀)
      (balancedDegreeList (10*(interiorFullWeight 3 3 q-1)-4*interiorFullWeight 3 3 q) 10) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀)
      (balancedDegreeList (10*(interiorFullWeight 3 3 q-1)-4*interiorFullWeight 3 3 q) 10) := by
  have hweight : interiorFullWeight 3 3 q=15*t := by
    rw [six_output_triple_weight,hdegree]
    omega
  have hseed := kernel_finrank_zero _ _ (poweredFiveFrame_kernel_zero (K:=K) t ht)
  have hbound := generic_six_output_triple_tangent_kernel_finrank_le_field_witness
    (K:=K) (E:=K) q (6*t-1) hq (poweredFiveFrame t)
    (fun i j => by rw [hdegree]; exact poweredFiveFrame_degree t i j)
  rw [hseed] at hbound
  have hzero := kernel_zero_of_finrank_zero _ _ (Nat.eq_zero_of_le_zero hbound)
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_six_output_triple_sl_tangent_factor (K:=K) q hq i₀
  have hbudget : (∑ i, e i)=Fintype.card (Fin 10)*
      ((interiorFullWeight 3 3 q-1)-(6*t-1)-1) := by
    rw [hweight] at hsum ⊢
    simp only [Fintype.card_fin]
    omega
  have he := reduced_factor_degrees_eq_of_kernel_vanishing_and_sum
    (polynomialKernelBasisMatrix _ B) C e (interiorFullWeight 3 3 q-1) (6*t-1)
    hV hlead hC hVC _ hAC hzero hbudget
  have hef : e=fun _ => 9*t-1 := by
    funext i
    have hi := he i
    rw [hweight] at hi
    omega
  have hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀) (List.replicate 10 (9*t-1)) := by
    refine ⟨10,B,e,hV,hlead,?_⟩
    rw [hef,List.ofFn_const]
  rw [hweight,balanced_uniform t ht]
  exact ⟨hmin,canonical_of_minimal q hq i₀ _ hmin⟩

end FD56
