/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PermutedSixOutputThreeTailWitness
import FD56.Hilbert.GenericSixOutputTangentTransfer
import FD56.Hilbert.GenericSixOutputCorankTwoTangentTransfer
import FD56.Hilbert.GenericSixOutputSLTangentCriterion
import FD56.Hilbert.GenericSixOutputCorankTwoSLTangentFactor
import FD56.LinearAlgebra.PowerSubstitutionKernel
import FD56.LinearAlgebra.ReducedFactorKernelTest

/-! Power substitution determines the six-output remainder-two and corank-two
families when the minor weight is divisible by six. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private def poweredThreeU (h : ℕ) : Fin 6 → K[X] :=
  fun i => Polynomial.expand K h (permutedSixOutputThreeTailU i)

private def poweredThreeV (h : ℕ) : Fin 6 → K[X] :=
  fun i => Polynomial.expand K h (permutedSixOutputThreeTailV i)

private theorem poweredThreeU_degree (h : ℕ) (i : Fin 6) :
    (poweredThreeU (K:=K) h i).natDegree≤3*h := by
  rw [poweredThreeU,Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right h (permutedSixOutputThreeTailU_degree i)

private theorem poweredThreeV_degree (h : ℕ) (i : Fin 6) :
    (poweredThreeV (K:=K) h i).natDegree≤3*h := by
  rw [poweredThreeV,Polynomial.natDegree_expand]
  exact Nat.mul_le_mul_right h (permutedSixOutputThreeTailV_degree i)

private theorem wedge_tangent_expand (h : ℕ) (u v : Fin 6 → K[X]) :
    sixOutputPluckerTangent (twoColumnWedge
      (fun i => Polynomial.expand K h (u i)) (fun i => Polynomial.expand K h (v i)))=
      (sixOutputPluckerTangent (twoColumnWedge u v)).map (Polynomial.expand K h) := by
  funext i j
  dsimp only [sixOutputPluckerTangent,Matrix.map_apply]
  split_ifs <;> simp [twoColumnWedge]

private theorem poweredThree_kernel_zero (h : ℕ) (hh : 0<h)
    (z : Fin 15 → K[X])
    (hz : sixOutputPluckerTangent (twoColumnWedge
      (poweredThreeU (K:=K) h) (poweredThreeV (K:=K) h))*ᵥz=0)
    (hdeg : ∀ j, (z j).natDegree≤2*h-1) : z=0 := by
  apply expanded_matrix_bounded_kernel_zero (permutedSixOutputThreeTailWitness (R:=K))
    1 h hh permutedSixOutputThreeTail_bounded_kernel_zero_charZero z
  · change sixOutputPluckerTangent (twoColumnWedge
      (fun i => Polynomial.expand K h (permutedSixOutputThreeTailU i))
      (fun i => Polynomial.expand K h (permutedSixOutputThreeTailV i)))*ᵥz=0 at hz
    rw [wedge_tangent_expand] at hz
    exact hz
  · simpa only [show h*(1+1)=2*h by omega] using hdeg

private theorem kernel_finrank_zero {F : Type*} [Field F]
    (P : Matrix (Fin 15) (Fin 15) F[X]) (d : ℕ)
    (hz : ∀ z : Fin 15 → F[X], P*ᵥz=0 → (∀ j, (z j).natDegree≤d) → z=0) :
    Module.finrank F (polynomialKernelAtDegree P d)=0 := by
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z h
  have he := hz (fun i => (z i).val) h (fun i => boundedPoly_degree d (z i))
  funext i
  exact Subtype.ext (congrFun he i)

private theorem kernel_zero_of_finrank_zero {F : Type*} [Field F]
    (P : Matrix (Fin 15) (Fin 15) F[X]) (d : ℕ)
    (hdim : Module.finrank F (polynomialKernelAtDegree P d)=0)
    (z : Fin 15 → F[X]) (hz : P*ᵥz=0) (hdeg : ∀ j, (z j).natDegree≤d) : z=0 := by
  let w : Fin 15 → BoundedPoly F d := fun j => boundedPolyOf (z j) (hdeg j)
  have hw : w∈polynomialKernelAtDegree P d := hz
  have hb : polynomialKernelAtDegree P d=⊥ := Submodule.finrank_eq_zero.mp hdim
  rw [hb,Submodule.mem_bot] at hw
  funext j
  exact congrArg Subtype.val (congrFun hw j)

private theorem balanced_uniform (h : ℕ) (hh : 0<h) :
    balancedDegreeList (9*(6*h-1)-3*(6*h)) 9=List.replicate 9 (4*h-1) := by
  have he : 9*(6*h-1)-3*(6*h)=9*(4*h-1) := by omega
  rw [he]
  simp [balancedDegreeList]

private theorem canonical_of_minimal {n : ℕ} (q : ℕ) (hq : 0<q)
    (i₀ : Fin n) (hlo : q*6<n) (hhi : n<(q+1)*6) (ys : List ℕ)
    (hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin 6))
      (genericAffineRows K (Fin n) (Fin 6)) i₀) ys) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin n) (Fin 6))
      (genericAffineRows K (Fin n) (Fin 6)) i₀) ys := by
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin n) (m:=Fin 6) q hq i₀
    (by simpa only [Fintype.card_fin] using hlo)
    (by simpa only [Fintype.card_fin] using hhi)
  have hp : xs.Perm ys := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ ys).mp hmin d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

theorem generic_six_output_sl_divisible_tangent_classification
    (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : twoColumnInteriorWeight 4 q=6*h) (i₀ : Fin (6*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*(twoColumnInteriorWeight 4 q-1)-3*twoColumnInteriorWeight 4 q) 9) := by
  have hseed := kernel_finrank_zero _ _ (poweredThree_kernel_zero (K:=K) h hh)
  have hbound := generic_six_output_tangent_kernel_finrank_le_field_witness
    (K:=K) (E:=K) q (3*h) (3*h) (2*h-1) hq (Or.inl rfl) (by omega)
    (poweredThreeU h) (poweredThreeV h) (poweredThreeU_degree h) (poweredThreeV_degree h)
  rw [hseed] at hbound
  have hzero := kernel_zero_of_finrank_zero _ _ (Nat.eq_zero_of_le_zero hbound)
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_six_output_sl_tangent_factor (K:=K) q hq i₀
  have hbudget : (∑ i, e i)=Fintype.card (Fin 9)*
      ((twoColumnInteriorWeight 4 q-1)-(2*h-1)-1) := by
    rw [hweight] at hsum ⊢
    simp only [Fintype.card_fin]
    omega
  have he := reduced_factor_degrees_eq_of_kernel_vanishing_and_sum
    (polynomialKernelBasisMatrix _ B) C e (twoColumnInteriorWeight 4 q-1) (2*h-1)
    hV hlead hC hVC _ hAC hzero hbudget
  have hef : e=fun _ => 4*h-1 := by
    funext i
    have hi := he i
    rw [hweight] at hi
    omega
  have hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀) (List.replicate 9 (4*h-1)) := by
    refine ⟨9,B,e,hV,hlead,?_⟩
    rw [hef,List.ofFn_const]
  rw [hweight,balanced_uniform h hh]
  exact ⟨hmin,canonical_of_minimal q hq i₀ (by omega) (by omega) _ hmin⟩

theorem generic_six_output_corank_two_sl_divisible_tangent_classification
    (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : interiorFullWeight 4 2 q=6*h) (i₀ : Fin (6*q+4)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*(interiorFullWeight 4 2 q-1)-3*interiorFullWeight 4 2 q) 9) := by
  have hseed := kernel_finrank_zero _ _ (poweredThree_kernel_zero (K:=K) h hh)
  have hbound := generic_six_output_corank_two_tangent_kernel_finrank_le_field_witness
    (K:=K) (E:=K) q (3*h) (3*h) (2*h-1) hq (Or.inl rfl) (by omega)
    (poweredThreeU h) (poweredThreeV h) (poweredThreeU_degree h) (poweredThreeV_degree h)
  rw [hseed] at hbound
  have hzero := kernel_zero_of_finrank_zero _ _ (Nat.eq_zero_of_le_zero hbound)
  obtain ⟨B,e,C,hV,hlead,_,hC,hVC,hAC,hsum⟩ :=
    generic_six_output_corank_two_sl_tangent_factor (K:=K) q hq i₀
  have hbudget : (∑ i, e i)=Fintype.card (Fin 9)*
      ((interiorFullWeight 4 2 q-1)-(2*h-1)-1) := by
    rw [hweight] at hsum ⊢
    simp only [Fintype.card_fin]
    omega
  have he := reduced_factor_degrees_eq_of_kernel_vanishing_and_sum
    (polynomialKernelBasisMatrix _ B) C e (interiorFullWeight 4 2 q-1) (2*h-1)
    hV hlead hC hVC _ hAC hzero hbudget
  have hef : e=fun _ => 4*h-1 := by
    funext i
    have hi := he i
    rw [hweight] at hi
    omega
  have hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀) (List.replicate 9 (4*h-1)) := by
    refine ⟨9,B,e,hV,hlead,?_⟩
    rw [hef,List.ofFn_const]
  rw [hweight,balanced_uniform h hh]
  exact ⟨hmin,canonical_of_minimal q hq i₀ (by omega) (by omega) _ hmin⟩

end FD56
