/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeGenericStack
import FD56.Hilbert.DepthThreeStackChange
import FD56.Hilbert.DepthTwoDeformedWitness

/-! Deformation of an independent three-row stack to an affine observability stack. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L m n : Type*} [Field K] [Field L]
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem depthThree_deformed_witness
    (φ : K[X] →+* L) (hφ : Function.Injective φ)
    (P Q T : Matrix m n K[X])
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2) (hT : DegreeBound T 3)
    (Mf M₀ : Matrix n n K[X]) (hMf : DegreeBound Mf 1) (hM₀ : DegreeBound M₀ 1)
    (A : Matrix m m K[X]) (D : Matrix m m K) (S : Matrix m (m ⊕ m) K[X])
    (hPM : P*Mf=A*P+D.map C*Q) (hM₀Q : P*M₀=Q)
    (hQM : Q*Mf=T+S*depthTwoStack P Q) :
    ∃ (M : Matrix n n L[X]) (P' : Matrix m n L[X]),
      DegreeBound M 1 ∧ DegreeBound P' 1 ∧
      ∀ d, Module.finrank L (polynomialKernelAtDegree (observabilityMatrix M P' 3) d) ≤
        Module.finrank K (polynomialKernelAtDegree (depthThreeStack P Q T) d) := by
  let σ := φ.comp C
  let ψ := Polynomial.mapRingHom σ
  let P' := P.map ψ
  let Q' := Q.map ψ
  let T' := T.map ψ
  let A' := A.map ψ
  let S' := S.map ψ
  let D' : Matrix m m L := D.map σ+φ X • 1
  let E' := D'⁻¹
  let M := Mf.map ψ+C (φ X) • M₀.map ψ
  have hDu : IsUnit D'.det := depthTwo_scalar_shift_isUnit_det φ hφ D
  have hED : E'*D'=1 := Matrix.nonsing_inv_mul D' hDu
  have hEDp : E'.map C*D'.map C=1 := by rw [← Matrix.map_mul,hED,Matrix.map_one] <;> simp
  have hDmap : D'.map C=(D.map C).map ψ+C (φ X) • (1 : Matrix m m L[X]) := by
    funext i j
    by_cases hij : i=j <;>
      simp [D',ψ,σ,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,hij]
  have hmapadd (U V : Matrix m n K[X]) : (U+V).map ψ=U.map ψ+V.map ψ := by
    funext i j
    exact map_add ψ _ _
  have hPM' : P'*Mf.map ψ=A'*P'+(D.map C).map ψ*Q' := by
    simpa only [hmapadd,Matrix.map_mul] using congrArg (fun Z => Z.map ψ) hPM
  have hM₀' : P'*M₀.map ψ=Q' := by
    simpa only [Matrix.map_mul] using congrArg (fun Z => Z.map ψ) hM₀Q
  have hmapstack : (depthTwoStack P Q).map ψ=depthTwoStack P' Q' := by
    funext i j
    cases i <;> rfl
  have hQM' : Q'*Mf.map ψ=T'+S'*depthTwoStack P' Q' := by
    simpa only [hmapadd,Matrix.map_mul,hmapstack] using
      congrArg (fun Z => Z.map ψ) hQM
  have hPMnew : P'*M=A'*P'+D'.map C*Q' := by
    simp only [M,Matrix.mul_add,Matrix.mul_smul,hPM',hM₀',hDmap,
      Matrix.add_mul,Matrix.smul_mul,Matrix.one_mul,add_assoc]
  have hQMnew : Q'*M=(T'+C (φ X) • (Q'*M₀.map ψ))+S'*depthTwoStack P' Q' := by
    simp only [M,Matrix.mul_add,Matrix.mul_smul,hQM']
    abel
  have hM : DegreeBound M 1 := by
    intro i j
    apply natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_map_le.trans (hMf i j)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (Polynomial.natDegree_map_le.trans (hM₀ i j))
  refine ⟨M,P',hM,fun i j => Polynomial.natDegree_map_le.trans (hP i j),?_⟩
  intro d
  rw [depthThree_stack_change_bounded_kernel M P' Q'
    (T'+C (φ X) • (Q'*M₀.map ψ)) A' (D'.map C) (E'.map C) S' hEDp hPMnew hQMnew d]
  let F := depthThreeStack P Q T
  let H := depthThreeStack (0 : Matrix m n K[X]) 0 (Q*M₀)
  have hF : ∀ i j, (F.transpose i j).natDegree≤depthThreeRowDegree j := by
    intro i j
    rcases j with (j | j) | j
    · exact hP j i
    · exact hQ j i
    · exact hT j i
  have hH : ∀ i j, (H.transpose i j).natDegree≤depthThreeRowDegree j := by
    intro i j
    rcases j with (j | j) | j
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact degreeBound_mul hQ hM₀ j i
  have hh := depthTwo_deformation_kernel_le φ hφ F.transpose H.transpose
    depthThreeRowDegree hF hH d
  have he : ((depthTwoPolynomialDeformation F.transpose H.transpose).map
      (Polynomial.mapRingHom φ)).transpose =
      depthThreeStack P' Q' (T'+C (φ X) • (Q'*M₀.map ψ)) := by
    rw [depthTwoPolynomialDeformation_map]
    have hm : (Q*M₀).map ψ=Q'*M₀.map ψ := by rw [Matrix.map_mul]
    funext i j
    rcases i with (i | i) | i
    · simp [F,H,depthThreeStack,depthTwoStack,Matrix.fromRows,P',ψ,σ]
    · simp [F,H,depthThreeStack,depthTwoStack,Matrix.fromRows,Q',ψ,σ]
    · change ψ (T i j)+C (φ X)*ψ ((Q*M₀) i j)=_
      exact congrArg (fun Z : Matrix m n L[X] => T' i j+C (φ X)*Z i j) hm
  rw [he,Matrix.transpose_transpose] at hh
  exact hh

end FD56
