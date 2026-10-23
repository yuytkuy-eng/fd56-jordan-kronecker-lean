/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoDeformation
import FD56.Hilbert.DepthTwoStackChange

/-! An actual affine depth-two witness with controlled terminal kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L m n r : Type*} [Field K] [Field L]
  [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n] [DecidableEq r]

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem depthTwoStack_map (σ : K →+* L) (P Q : Matrix m n K[X]) :
    (depthTwoStack P Q).map (Polynomial.mapRingHom σ) =
      depthTwoStack (P.map (Polynomial.mapRingHom σ)) (Q.map (Polynomial.mapRingHom σ)) := by
  funext i j
  cases i <;> rfl

theorem depthTwo_deformed_witness
    (φ : K[X] →+* L) (hφ : Function.Injective φ)
    (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (a : r → ℕ)
    (hV : ∀ x j, (polynomialKernelBasisMatrix (depthTwoStack P Q) B x j).natDegree ≤ a j)
    (Mf M₀ : Matrix n n K[X]) (hMf : DegreeBound Mf 1) (hM₀ : DegreeBound M₀ 1)
    (A : Matrix m m K[X]) (D : Matrix m m K) (hA : DegreeBound A 1)
    (hfactor : P * Mf = A * P + D.map C * Q) (hM₀Q : P * M₀ = Q)
    (hzero : P * Mf * polynomialKernelBasisMatrix (depthTwoStack P Q) B = 0) :
    let ψ := Polynomial.mapRingHom (φ.comp C)
    let P' := P.map ψ
    ∃ (M : Matrix n n L[X])
      (B' : Basis r L[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P' (P' * M)))))
      (R' : Matrix n (m ⊕ m) L[X]),
      DegreeBound M 1 ∧ DegreeBound P' 1 ∧
      depthTwoStack P' (P' * M) * R' = 1 ∧
      polynomialKernelBasisMatrix _ B' =
        (polynomialKernelBasisMatrix (depthTwoStack P Q) B).map ψ ∧
      Function.Injective (Matrix.mulVec (fun x i =>
        (depthTwoStack P' (P' * M) i x).coeff (depthTwoRowDegree i))) ∧
      ∀ d, Module.finrank L (polynomialKernelAtDegree
          (P' * M ^ 2 * polynomialKernelBasisMatrix _ B').transpose d) ≤
        Module.finrank K (polynomialKernelAtDegree
          (Q * Mf * polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose d) := by
  let σ := φ.comp C
  let ψ := Polynomial.mapRingHom σ
  let P' := P.map ψ
  let Q' := Q.map ψ
  let V := polynomialKernelBasisMatrix (depthTwoStack P Q) B
  let V' := V.map ψ
  let A' := A.map ψ
  let D' : Matrix m m L := D.map σ + φ X • 1
  let E' := D'⁻¹
  let M := (depthTwoPolynomialDeformation Mf M₀).map (Polynomial.mapRingHom φ)
  let F := Q * Mf * V
  let H := Q * M₀ * V
  have hDunit : IsUnit D'.det := depthTwo_scalar_shift_isUnit_det φ hφ D
  have hDE : D' * E' = 1 := Matrix.mul_nonsing_inv D' hDunit
  have hED : E' * D' = 1 := Matrix.nonsing_inv_mul D' hDunit
  have hDmap : D'.map C = (D.map C).map ψ + C (φ X) • (1 : Matrix m m L[X]) := by
    funext i j
    by_cases hij : i=j <;>
      simp [D',ψ,σ,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply,
        Matrix.one_apply,hij]
  have hM : M = Mf.map ψ + C (φ X) • M₀.map ψ :=
    depthTwoPolynomialDeformation_map φ Mf M₀
  have hP' : DegreeBound P' 1 := fun i j => Polynomial.natDegree_map_le.trans (hP i j)
  have hQ' : DegreeBound Q' 2 := fun i j => Polynomial.natDegree_map_le.trans (hQ i j)
  have hA' : DegreeBound A' 1 := fun i j => Polynomial.natDegree_map_le.trans (hA i j)
  have hMdeg : DegreeBound M 1 := by
    intro i j
    apply Polynomial.natDegree_map_le.trans
    exact depthTwoPolynomialDeformation_degree Mf M₀ (fun _ => 1) hMf hM₀ i j
  have hQV : Q * V = 0 := by
    funext i j
    exact congrFun (congrFun (polynomialKernelBasisMatrix_mul (depthTwoStack P Q) B) (Sum.inr i)) j
  have hfac' : P' * Mf.map ψ = A' * P' + (D.map C).map ψ * Q' := by
    have hh := congrArg (fun Z => Z.map ψ) hfactor
    dsimp only at hh
    rw [Matrix.map_mul] at hh
    have hadd : (A * P + D.map C * Q).map ψ =
        (A * P).map ψ + (D.map C * Q).map ψ := by
      funext i j
      exact map_add ψ _ _
    rw [hadd,Matrix.map_mul,Matrix.map_mul] at hh
    exact hh
  have hM₀' : P' * M₀.map ψ = Q' := by
    simpa only [Matrix.map_mul] using congrArg (fun Z => Z.map ψ) hM₀Q
  have hz' : P' * Mf.map ψ * V' = 0 := by
    simpa only [Matrix.map_mul,Matrix.map_zero,map_zero] using congrArg (fun Z => Z.map ψ) hzero
  have hQV' : Q' * V' = 0 := by
    simpa only [Matrix.map_mul,Matrix.map_zero,map_zero] using congrArg (fun Z => Z.map ψ) hQV
  obtain ⟨hPM,hPMV,hterminal⟩ := depthTwo_deformation_identities P' Q' V'
    (Mf.map ψ) (M₀.map ψ) A' ((D.map C).map ψ) (C (φ X)) hfac' hM₀' hz' hQV'
  rw [← hM,← hDmap] at hPM hterminal
  have haux : Q' * Mf.map ψ * V' + C (φ X) • (Q' * M₀.map ψ * V') =
      (depthTwoPolynomialDeformation F H).map (Polynomial.mapRingHom φ) := by
    rw [depthTwoPolynomialDeformation_map]
    simp only [F,H,Matrix.map_mul]
    rfl
  rw [haux] at hterminal
  have hbase := polynomial_kernel_basis_map σ (depthTwoStack P Q) B R hR
  rw [depthTwoStack_map] at hbase
  obtain ⟨B₁,hB₁⟩ := hbase
  have hR₁ : depthTwoStack P' Q' * R.map ψ = 1 := by
    rw [← depthTwoStack_map, ← Matrix.map_mul, hR, Matrix.map_one] <;> simp
  have hDEp : D'.map C * E'.map C = 1 := by rw [← Matrix.map_mul,hDE,Matrix.map_one] <;> simp
  have hEDp : E'.map C * D'.map C = 1 := by rw [← Matrix.map_mul,hED,Matrix.map_one] <;> simp
  have hchange := depthTwo_stack_change_basis P' Q' B₁ (R.map ψ) hR₁
    A' (D'.map C) (E'.map C) hDEp hEDp
  rw [← hPM] at hchange
  obtain ⟨B₂,R₂,hB₂,hR₂⟩ := hchange
  have hlead' : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P' Q' i x).coeff (depthTwoRowDegree i))) := by
    have h := matrix_injective_of_field_specialization (RingHom.id K) σ σ.injective
      (show Matrix n (m ⊕ m) K from fun x i =>
        (depthTwoStack P Q i x).coeff (depthTwoRowDegree i)) (by simpa using hlead)
    have he : (show Matrix n (m ⊕ m) L from fun x i =>
        (depthTwoStack P' Q' i x).coeff (depthTwoRowDegree i)) =
        (show Matrix n (m ⊕ m) K from fun x i =>
          (depthTwoStack P Q i x).coeff (depthTwoRowDegree i)).map σ := by
      funext x i
      cases i <;> simp [depthTwoStack,P',Q',ψ,Matrix.map_apply,Polynomial.coeff_map]
    dsimp only at he
    rw [he]
    exact h
  have hlead₂ := depthTwo_stack_change_leading P' Q' A' D' E' hDE hED hP' hQ' hA' hlead'
  rw [← hPM] at hlead₂
  refine ⟨M,B₂,R₂,hMdeg,hP',hR₂,hB₂.trans hB₁,hlead₂,?_⟩
  intro d
  rw [hB₂,hB₁,hterminal,constant_left_mul_kernel_hilbert D' E' hDE hED]
  apply depthTwo_deformation_kernel_le φ hφ F H (fun j => a j + 3)
  · intro i j
    have h := (matrixCoeff_mul_column (Q * Mf) V 3 a (degreeBound_mul hQ hMf) hV i j).1
    simpa only [Nat.add_comm] using h
  · intro i j
    have h := (matrixCoeff_mul_column (Q * M₀) V 3 a (degreeBound_mul hQ hM₀) hV i j).1
    simpa only [Nat.add_comm] using h

end FD56
