/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericInteriorDifferentialRank
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Hilbert.GenericTerminalDegreeBudget
import FD56.LinearAlgebra.PluckerDegreeBalance
import FD56.LinearAlgebra.ComplementaryKernelMinorReindex
import FD56.Stabilizer.InteriorTerminalRowEquiv

/-! The two actual auxiliary reduced bases in every generic interior range
have pairwise balanced degrees. The proof compares their Plucker derivative
bounds with the derivative rank forced by the SL kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 1000000

variable (r s q : ℕ) [NeZero r] [NeZero s]
variable {K : Type*} [Field K]

theorem generic_interior_auxiliary_degrees_balanced (hq : 0 < q)
    (Bv : Basis (Fin r)
      (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))
        (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s))) q))))
    (Bt : Basis (Fin s)
      (AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s))))[X]
      (LinearMap.ker (Matrix.toLin'
        (genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s)) *
          (genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s)))^q *
          polynomialKernelBasisMatrix _ Bv).transpose)))
    (a : Fin r → ℕ) (b : Fin s → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix _ Bv i j).natDegree ≤ a j)
    (hT : ∀ i j, (polynomialKernelBasisMatrix _ Bt i j).natDegree ≤ b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ Bv i j).coeff (a j))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ Bt i j).coeff (b j)))) :
    (∀ i j, a i ≤ a j + 1) ∧ (∀ i j, b i ≤ b j + 1) := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin ((r+s)*q+r)) (Fin (r+s)))
  let M := genericAffineSquare K (Fin ((r+s)*q+r)) (Fin (r+s))
  let P := genericAffineRows K (Fin ((r+s)*q+r)) (Fin (r+s))
  let O := observabilityMatrix M P q
  let V := polynomialKernelBasisMatrix O Bv
  let G := P*M^q*V
  let T := polynomialKernelBasisMatrix G.transpose Bt
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
  have hminV : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨r, Bv, a, hV, hVL, List.Perm.refl _⟩
  have hminT : HasMinimalKernelDegrees G.transpose (List.ofFn b) :=
    ⟨s, Bt, b, hT, hTL, List.Perm.refl _⟩
  have hbudget := (generic_observability_kernel_degree_budget q hlo _ hminV).2
  simp only [List.sum_ofFn, Fintype.card_fin] at hbudget
  have hW : 2*W=(r+s)*q*(q+1)+2*(q+1)*r := by
    dsimp only [W]
    nlinarith
  have hsumG : (∑ i, d i)=W := by
    simp only [d, W, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  have hsumT : (∑ i, b i)=W := by
    simpa only [List.sum_ofFn, Fintype.card_fin] using
      (generic_terminal_kernel_degree_budget q hm hlo hhi Bv a hV hVL _ hminT).2
  have hGdegree :=
    (generic_terminal_kernel_degree_and_leading q hhi.le Bv a hV hVL).1
  obtain ⟨LG, hLG⟩ := generic_terminal_kernel_left_inverse q hm hlo hhi Bv
  change LG*G=1 at hLG
  have hGinj : Function.Injective G.mulVec := by
    intro u v huv
    have h := congrArg LG.mulVec huv
    simpa only [Matrix.mulVec_mulVec, hLG, Matrix.one_mulVec] using h
  obtain ⟨R, hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c, _, hc⟩ := interior_selected_minors_common_scalar r s q M P R hR Bv
  have hminor : genericInteriorMinorVector (K:=K) r s q =
      fun z => C c*pluckerMinorVector G (interiorTerminalRow r s z) := funext hc
  have hlower := generic_interior_minor_derivation_rank_lower_of_weight (K:=K) r s q hq W hW
  have hbalG : ∀ i j, d i ≤ d j+1 := by
    apply polynomial_derivation_selected_plucker_degrees_balanced (K:=K)
      (interiorTerminalRow r s) c G d hGdegree hGinj (by simp)
    rw [← hminor]
    simpa only [Fintype.card_fin, hsumG, Nat.add_sub_cancel_left, Nat.mul_comm s r,
      Nat.add_assoc] using hlower
  have hbalV : ∀ i j, a i ≤ a j+1 := by
    intro i j
    have h := hbalG i j
    dsimp only [d] at h
    omega
  let e : Fin (r+s) ≃ Fin r ⊕ Fin s := finSumFinEquiv.symm
  let rows := interiorTerminalRowEquiv r s
  let sign : Option (Fin r × Fin s) → K :=
    fun z => ((Equiv.Perm.sign ((rows z).trans e) : ℤ) : K)
  let rowT : Option (Fin r × Fin s) → Fin s → Fin (r+s) :=
    fun z j => rows z (Sum.inr j)
  obtain ⟨cT, _, hcT⟩ := polynomial_dual_basis_selected_complementary_minors
    (K:=K) G LG hLG Bt e rows
  have hminorT : genericInteriorMinorVector (K:=K) r s q =
      fun z => C (algebraMap K L (sign z))*C (c*cT)*pluckerMinorVector T (rowT z) := by
    funext z
    rw [hminor]
    dsimp only
    have h := hcT z
    have hrow : (fun j => rows z (Sum.inl j))=interiorTerminalRow r s z := by
      funext j
      exact interiorTerminalRowEquiv_inl r s z j
    rw [hrow] at h
    change pluckerMinorVector G (interiorTerminalRow r s z)=
      C (algebraMap K L (sign z))*C cT*pluckerMinorVector T (rowT z) at h
    rw [h, Polynomial.C_mul]
    ring
  have hTinj : Function.Injective T.mulVec := polynomialKernelBasisMatrix_injective _ Bt
  have hbalT : ∀ i j, b i ≤ b j+1 := by
    apply polynomial_derivation_signed_plucker_degrees_balanced (K:=K)
      rowT sign (c*cT) T b hT hTinj (by simp)
    rw [← hminorT]
    simpa only [Fintype.card_fin, hsumT, Nat.add_sub_cancel_right, Nat.add_assoc] using hlower
  exact ⟨hbalV, hbalT⟩

end FD56
