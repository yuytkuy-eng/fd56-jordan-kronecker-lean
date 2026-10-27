/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.OneOutputGLHalfspace
import FD56.Hilbert.SeparableIsotropicBlock
import FD56.Stabilizer.ScalarGLDeterminant

/-! The generic one-output GL pencil consists of N(N+1)/2 distinct simple regular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

set_option maxHeartbeats 1000000 in
theorem generic_one_output_gl_jordan_decomposition (K : Type*) [Field K]
    (N : ℕ) (hN : 0<N) :
    ∃ p : (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1)))[X],
      p.Separable ∧ p.natDegree=N*(N+1)/2 ∧
    let L := p.SplittingField
    ∃ lam : Fin (N*(N+1)/2) → L, Function.Injective lam ∧
    ∃ Q : Matrix (SLInput (Fin N) (Fin 1)) ((Fin 1 ⊕ Fin 1) × Fin (N*(N+1)/2)) L,
    ∃ R : Matrix ((Fin 1 ⊕ Fin 1) × Fin (N*(N+1)/2)) (SLInput (Fin N) (Fin 1)) L,
      Q*R=1 ∧ R*Q=1 ∧
      (Q.map C).transpose *
        (glKirillovMatrix (genericAffineSquare K (Fin N) (Fin 1))
          (genericAffineRows K (Fin N) (Fin 1))).map
          (Polynomial.mapRingHom (algebraMap _ L)) * Q.map C =
        Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1) := by
  classical
  let F := AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1))
  let d := N*(N+1)/2
  let H := glKirillovMatrix (genericAffineSquare K (Fin N) (Fin 1))
    (genericAffineRows K (Fin N) (Fin 1))
  let g := (observabilitySelectedMatrix (genericAffineSquare K (Fin N) (Fin 1))
    (genericAffineRows K (Fin N) (Fin 1)) Fin.val (fun _ => 0)).det
  obtain ⟨S,T,A,W,hST,hTS,hcong,hA,hW,halt⟩ :=
    generic_one_output_gl_isotropic_block_form (K := K) N hN
  have hdim : Fintype.card (Fin d ⊕ Fin d)=Fintype.card (SLInput (Fin N) (Fin 1)) := by
    simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,mul_one]
    dsimp only [d]
    rw [← oneOutputWeight_eq]
    nlinarith [oneOutputWeight_twice N]
  let e : (Fin d ⊕ Fin d) ≃ SLInput (Fin N) (Fin 1) := Fintype.equivOfCardEq hdim
  have hg : g.Separable := (generic_scalar_observability_separable K N).2
  have hgd : g.natDegree=Fintype.card (Fin d) := by
    rw [(generic_scalar_observability_separable K N).1]
    simpa only [oneOutputWeight,d,Fintype.card_fin] using oneOutputWeight_eq N
  obtain ⟨hsep,hW₁⟩ := isotropic_cross_determinant_separable e S T hST H A W hcong hW g
    (generic_scalar_gl_kirillov_determinant K N) hg hgd
  let A₀ : Matrix (Fin d) (Fin d) F := fun i j => (A i j).coeff 0
  let A₁ : Matrix (Fin d) (Fin d) F := fun i j => (A i j).coeff 1
  let W₀ : Matrix (Fin d) (Fin d) F := fun i j => (W i j).coeff 0
  let W₁ : Matrix (Fin d) (Fin d) F := fun i j => (W i j).coeff 1
  have hWA : affineMatrixPencil W₀ W₁=W := affineMatrixPencil_coefficients W hW
  have hAA : affineMatrixPencil A₀ A₁=A := affineMatrixPencil_coefficients A hA
  have hcross : alternatingCrossPencil A₀ A₁ W₀ W₁=Matrix.fromBlocks A W (-W.transpose) 0 := by
    rw [alternatingCrossPencil,hWA,hAA]
  have hs : (affineMatrixPencil W₀ W₁).det.Separable := by rwa [hWA]
  let p := (-W₁⁻¹*W₀).charpoly
  have hp : p.Separable := affine_ratio_charpoly_separable W₀ W₁ _
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hW₁)) hs
  refine ⟨p,hp,by simpa [p,d] using (-W₁⁻¹*W₀).charpoly_natDegree_eq_dim,?_⟩
  let L := p.SplittingField
  let φ : F →+* L := algebraMap F L
  let ψ := Polynomial.mapRingHom φ
  obtain ⟨lam,hlam,U,V,hUV,hVU,hjordan⟩ :=
    alternatingCrossPencil_separable_jordan_decomposition A₀ A₁ W₀ W₁
      (halt 0) (halt 1) hW₁ hs
  let S' := S.map φ
  let T' := T.map φ
  have hST' : S'*T'=1 := by
    dsimp only [S',T']
    rw [← Matrix.map_mul,hST,Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hTS' : T'*S'=1 := by
    dsimp only [S',T']
    rw [← Matrix.map_mul,hTS,Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hmap (B : Matrix (SLInput (Fin N) (Fin 1)) (Fin d ⊕ Fin d) F) :
      (B.map C).map ψ=(B.map φ).map C := by
    funext i j
    exact Polynomial.map_C φ
  have hbase : (S'.map C).transpose*H.map ψ*S'.map C=
      (alternatingCrossPencil A₀ A₁ W₀ W₁).map ψ := by
    have hh := congrArg (fun B => B.map ψ) hcong
    dsimp only at hh
    rw [Matrix.map_mul,Matrix.map_mul,Matrix.transpose_map,hmap] at hh
    rw [hcross]
    exact hh
  refine ⟨lam,hlam,S'*U,V*T',?_,?_,?_⟩
  · calc
      S'*U*(V*T')=S'*(U*V)*T' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUV,Matrix.mul_one,hST']
  · calc
      V*T'*(S'*U)=V*(T'*S')*U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTS',Matrix.mul_one,hVU]
  · rw [Matrix.map_mul,Matrix.transpose_mul]
    change (U.map C).transpose*(S'.map C).transpose*H.map ψ*(S'.map C*U.map C)=_
    calc
      _ = (U.map C).transpose*((S'.map C).transpose*H.map ψ*S'.map C)*U.map C := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hbase]; exact hjordan

end FD56
