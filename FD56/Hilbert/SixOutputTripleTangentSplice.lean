/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialTailSplice
import FD56.LinearAlgebra.PolynomialTailKernelResidue
import FD56.LinearAlgebra.SixOutputTripleTangentFunctor
import FD56.Hilbert.PolynomialKernelResidueDimension

/-! A three-column tail splice and its bounded tangent-kernel dimension inequality. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000
variable {K : Type*} [Field K]

def sixOutputTripleSpliceFrame (G U : Matrix (Fin 6) (Fin 3) K[X]) (h : ℕ) :
    Matrix (Fin 6) (Fin 3) K[X][X] :=
  fun i j => polynomialTailSplice (G i j) (U i j) h

def sixOutputTripleSpliceTangent (G U : Matrix (Fin 6) (Fin 3) K[X]) (h : ℕ) :
    Matrix (Fin 20) (Fin 20) K[X][X] :=
  sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors (sixOutputTripleSpliceFrame G U h))

private theorem splice_parameter_zero (G U : Matrix (Fin 6) (Fin 3) K[X]) (h : ℕ) :
    (sixOutputTripleSpliceTangent G U h).map (Polynomial.mapRingHom (Polynomial.evalRingHom 0))=
      (X : K[X])^(h*3) • sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G) := by
  unfold sixOutputTripleSpliceTangent
  rw [sixOutputTripleTangent_frame_map]
  have he : (sixOutputTripleSpliceFrame G U h).map
      (Polynomial.mapRingHom (Polynomial.evalRingHom 0))=(X : K[X])^h • G := by
    apply Matrix.ext
    intro i j
    exact polynomialTailSplice_parameter_zero _ _ _
  rw [he,sixOutputTripleTangent_frame_smul,pow_mul]

theorem six_output_triple_tangent_splice_residue_shift
    (G U : Matrix (Fin 6) (Fin 3) K[X]) (h k d : ℕ) (hk : 0<k)
    (hU : ∀ i j, (U i j).natDegree≤h)
    (hmatch : ∀ i j, (U i j).coeff h=(G i j).coeff 0)
    (hzero : ∀ z : Fin 20 → K[X],
      sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors U)*ᵥz=0 →
      (∀ j, (z j).natDegree≤k-1) → z=0)
    (H : Fin 20 → K[X][X]) (hPH : sixOutputTripleSpliceTangent G U h*ᵥH=0)
    (hdeg : ∀ j, (H j).natDegree≤d+k) :
    ∃ z : Fin 20 → K[X],
      sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)*ᵥz=0 ∧
      (∀ j, (z j).natDegree≤d) ∧
      (fun j => (H j).map (Polynomial.evalRingHom 0))=(X : K[X])^k • z := by
  let V : Matrix (Fin 6) (Fin 3) K[X][X] :=
    fun i j => polynomialTailSpliceQuotient (G i j) (U i j) h
  let Q := sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors V)
  have hQ : (fun i j => (Q i j).coeff 0)=sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors U) := by
    change Q.map Polynomial.constantCoeff=_
    rw [sixOutputTripleTangent_frame_map]
    have he : V.map Polynomial.constantCoeff=U := by
      apply Matrix.ext
      intro i j
      exact polynomialTailSpliceQuotient_constant _ _ _ (hU i j) (hmatch i j)
    rw [he]
  have hfactor : (sixOutputTripleSpliceTangent G U h).map bivariateDiagonalRescaling=
      ((X : K[X][X])^h)^3 • Q := by
    unfold sixOutputTripleSpliceTangent
    rw [sixOutputTripleTangent_frame_map]
    have he : (sixOutputTripleSpliceFrame G U h).map bivariateDiagonalRescaling=
        (X : K[X][X])^h • V := by
      apply Matrix.ext
      intro i j
      exact polynomialTailSplice_diagonal_factor _ _ _
    rw [he,sixOutputTripleTangent_frame_smul]
  have hQH : Q*ᵥ(fun j => bivariateDiagonalRescaling (H j))=0 := by
    have hm : ((sixOutputTripleSpliceTangent G U h).map bivariateDiagonalRescaling)*ᵥ
        (fun j => bivariateDiagonalRescaling (H j))=0 := by
      funext i
      have he := congrArg bivariateDiagonalRescaling (congrFun hPH i)
      simpa [RingHom.map_mulVec,Function.comp_def] using he
    rw [hfactor,Matrix.smul_mulVec_assoc] at hm
    funext i
    have he := congrFun hm i
    change (X^h)^3*(Q*ᵥ(fun j => bivariateDiagonalRescaling (H j))) i=0 at he
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 (pow_ne_zero h Polynomial.X_ne_zero))
  have hdiv := polynomial_tail_kernel_residue_divisible Q H k hk hQH (by rw [hQ]; exact hzero)
  exact polynomial_kernel_shift_of_residue_divisible
    (sixOutputTripleSpliceTangent G U h)
    (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) H (h*3) k d
    (splice_parameter_zero G U h) hPH hdiv hdeg

theorem six_output_triple_tangent_splice_kernel_finrank_le
    {F : Type*} [Field F] [Algebra K[X] F] [IsFractionRing K[X] F]
    (G U : Matrix (Fin 6) (Fin 3) K[X]) (h k d : ℕ) (hk : 0<k)
    (hU : ∀ i j, (U i j).natDegree≤h)
    (hmatch : ∀ i j, (U i j).coeff h=(G i j).coeff 0)
    (hzero : ∀ z : Fin 20 → K[X],
      sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors U)*ᵥz=0 →
      (∀ j, (z j).natDegree≤k-1) → z=0) :
    Module.finrank F (polynomialKernelAtDegree
      ((sixOutputTripleSpliceTangent G U h).map
        (Polynomial.mapRingHom (algebraMap K[X] F))) (d+k)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) := by
  apply polynomial_kernel_finrank_le_of_residue_divisible
    (sixOutputTripleSpliceTangent G U h)
    (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) (h*3) k d
    (splice_parameter_zero G U h)
  intro H hPH hdeg
  obtain ⟨z,_,_,hres⟩ := six_output_triple_tangent_splice_residue_shift
    G U h k d hk hU hmatch hzero H hPH hdeg
  intro j
  exact ⟨z j,congrFun hres j⟩

end FD56
