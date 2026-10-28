/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDegreeBalance
import FD56.LinearAlgebra.PluckerDifferentialImage

/-! Actual generic coefficient variations exhaust the selected Plucker
differential of the terminal matrix with its proved column degree bounds. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 1000000

variable (r s q : ℕ) [NeZero r] [NeZero s]
variable {K : Type*} [Field K]

theorem generic_interior_minor_derivation_image (hq : 0 < q)
    (B : Basis (Fin r)
      (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
        (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s))) q))))
    (a : Fin r → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree ≤ a j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (a j)))) :
    let G := genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s)) *
      (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))^q *
        polynomialKernelBasisMatrix _ B
    ∃ c : AffineCoefficientField K
        (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))), c≠0 ∧
      genericInteriorMinorVector (K:=K) r s q =
        (fun z => C c*pluckerMinorVector G (interiorTerminalRow r s z)) ∧
      LinearMap.range (polynomialDerivationImageMap (K:=K)
        (genericInteriorMinorVector (K:=K) r s q)) =
        LinearMap.range ((signedPluckerProjection (interiorTerminalRow r s)
          (fun _ => (1:K))).comp (weightedPluckerDifferential c G (fun i => a i+q+1))) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)))
  let M := genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s))
  let P := genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s))
  let O := observabilityMatrix M P q
  let V := polynomialKernelBasisMatrix O B
  let G := P*M^q*V
  let d : Fin r → ℕ := fun i => a i+q+1
  let W := (∑ i, a i)+(q+1)*r
  have hr : 0 < r := NeZero.pos r
  have hs : 0 < s := NeZero.pos s
  have hm : 2 ≤ Fintype.card (Fin (r+s)) := by simp only [Fintype.card_fin]; omega
  have hlo : q*Fintype.card (Fin (r+s)) < Fintype.card (Fin ((r+s)*q+r)) := by
    simp only [Fintype.card_fin]
    nlinarith
  have hhi : Fintype.card (Fin ((r+s)*q+r)) < (q+1)*Fintype.card (Fin (r+s)) := by
    simp only [Fintype.card_fin]
    nlinarith
  have hmin : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨r,B,a,hV,hVL,List.Perm.refl _⟩
  have hbudget := (generic_observability_kernel_degree_budget q hlo _ hmin).2
  simp only [List.sum_ofFn,Fintype.card_fin] at hbudget
  have hW : 2*W=(r+s)*q*(q+1)+2*(q+1)*r := by
    dsimp only [W]
    nlinarith
  have hsum : (∑ i, d i)=W := by
    simp only [d,W,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    ring
  have hdegree := (generic_terminal_kernel_degree_and_leading q hhi.le B a hV hVL).1
  obtain ⟨LG,hLG⟩ := generic_terminal_kernel_left_inverse q hm hlo hhi B
  change LG*G=1 at hLG
  have hG : Function.Injective G.mulVec := by
    intro u v huv
    have h := congrArg LG.mulVec huv
    simpa only [Matrix.mulVec_mulVec,hLG,Matrix.one_mulVec] using h
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,hc,hminor⟩ := interior_selected_minors_common_scalar r s q M P R hR B
  have he : genericInteriorMinorVector (K:=K) r s q =
      fun z => C c*pluckerMinorVector G (interiorTerminalRow r s z) := funext hminor
  have he' : (fun z => C (algebraMap K L (1:K))*C c*
      pluckerMinorVector G (interiorTerminalRow r s z)) =
      genericInteriorMinorVector (K:=K) r s q := by
    rw [he]
    funext z
    simp
  refine ⟨c,hc,he,?_⟩
  have hlower := generic_interior_minor_derivation_rank_lower_of_weight (K:=K) r s q hq W hW
  have h := polynomial_derivation_range_eq_weighted_plucker_range (K:=K)
    (interiorTerminalRow r s) (fun _ => (1:K)) c G d hdegree hG (by simp) (by
      rw [he']
      simpa only [Fintype.card_fin,hsum,Nat.add_sub_cancel_left,Nat.mul_comm s r,
        Nat.add_assoc] using hlower)
  rw [he'] at h
  exact h

end FD56
