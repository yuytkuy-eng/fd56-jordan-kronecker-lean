/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleGLTraceSupport
import FD56.Stabilizer.GenericDivisibleSLDegrees
import FD56.Hilbert.RankTwoTraceCovectorCoordinates
import FD56.Hilbert.MinimalDegreeExtension

/-! The actual trace meets every primary block of a divisible generic GL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K L : Type*} {m : Type} [Field K] [Field L] [IsAlgClosed L]
  [Fintype m] [DecidableEq m]

local instance genericDivisibleSLActiveTraceDecidableEq : DecidableEq L := Classical.decEq L

set_option maxHeartbeats 3000000 in
theorem generic_divisible_gl_jordan_active_trace (q : ℕ) (hm : 2≤Fintype.card m)
    (φ : AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m) →+* L) :
    let H := (glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m)).map (Polynomial.mapRingHom φ)
    let f := polynomialPencilOperator H
    ∃ T : Matrix (SLInput (Fin (q+1) × m) m)
      (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2)) L,
    ∃ S : Matrix (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2))
      (SLInput (Fin (q+1) × m) m) L,
    ∃ c d : f.Eigenvalues → L,
      T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*H*T.map C=
        Matrix.blockDiagonal' (fun a : f.Eigenvalues => rankTwoJordanPencil a.val (Fintype.card m-2)) ∧
      (∀ v, slInputTrace L L (T *ᵥ v)=rankTwoTraceSumCovector c d (Fintype.card m-2) ⬝ᵥ v) ∧
      (∀ a, c a≠0 ∨ d a≠0) := by
  classical
  let M := genericAffineSquare K (Fin (q+1) × m) m
  let P := genericAffineRows K (Fin (q+1) × m) m
  let H := (glKirillovMatrix M P).map (Polynomial.mapRingHom φ)
  let f := polynomialPencilOperator H
  let J := Matrix.blockDiagonal' (fun a : f.Eigenvalues =>
    rankTwoJordanPencil a.val (Fintype.card m-2))
  obtain ⟨T,S,c,d,hTS,hST,hcong,hcoords⟩ := generic_divisible_gl_jordan_trace_support q hm φ
  let cv := rankTwoTraceSumCovector c d (Fintype.card m-2)
  have htrace : ∀ v, slInputTrace L L (T*ᵥv)=cv ⬝ᵥ v := by
    intro v
    rw [hcoords,rankTwoTraceSumCovector_dotProduct]
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp (show 0<Fintype.card m by omega)
  let i₀ : Fin (q+1) × m := (0,r)
  let B : Matrix (SLInput (Fin (q+1) × m) m) (SLChartInput (Fin (q+1) × m) m i₀) L :=
    slChartEmbeddingMatrix i₀
  let R : Matrix (SLChartInput (Fin (q+1) × m) m i₀) (SLInput (Fin (q+1) × m) m) L :=
    slChartRetractionMatrix i₀
  let E := S*B
  let F := R*T
  have hTE : T*E=B := by simp only [E,← Matrix.mul_assoc,hTS,Matrix.one_mul]
  have hEtrace : ∀ v, cv ⬝ᵥ (E*ᵥv)=0 := by
    intro v
    rw [← htrace,Matrix.mulVec_mulVec,hTE]
    change slInputTrace L L (slChartEmbeddingMatrix i₀*ᵥv)=0
    rw [slChartEmbeddingMatrix_mulVec,slChartEmbed_trace]
  have hE : E.transpose*ᵥcv=0 := by
    funext j
    have hz := hEtrace (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at hz
    simpa only [dotProduct,Matrix.mulVec,Matrix.transpose_apply,
      Pi.zero_apply,mul_comm] using hz
  have hEF : ∀ v, cv ⬝ᵥ v=0 → E*ᵥ(F*ᵥv)=v := by
    intro v hv
    have ht : slInputTrace L L (T*ᵥv)=0 := (htrace v).trans hv
    have hrec : B*ᵥ(R*ᵥ(T*ᵥv))=T*ᵥv := by
      change slChartEmbeddingMatrix i₀*ᵥ(slChartRetractionMatrix i₀*ᵥ(T*ᵥv))=T*ᵥv
      rw [slChartRetractionMatrix_mulVec,slChartEmbeddingMatrix_mulVec]
      exact slChartEmbed_retract L L i₀ (T*ᵥv) ht
    simp only [E,F,← Matrix.mulVec_mulVec]
    rw [hrec,Matrix.mulVec_mulVec,hST,Matrix.one_mulVec]
  have hEC : T.map C*E.map C=B.map C := by
    rw [← Matrix.map_mul,hTE]
  have hcongJ : (T.map C).transpose*H*T.map C=J := hcong
  have hres : (E.map C).transpose*J*E.map C=
      (slKirillovMatrix M P i₀).map (Polynomial.mapRingHom φ) := by
    calc
      _ = (B.map C).transpose*H*B.map C := by
        rw [← hcongJ]
        calc
          _ = (T.map C*E.map C).transpose*H*(T.map C*E.map C) := by
            simp only [Matrix.transpose_mul,Matrix.mul_assoc]
          _ = _ := by rw [hEC]
      _ = _ := by
        simp only [H,slKirillovMatrix,Matrix.map_mul,Matrix.transpose_map,
          slChartEmbeddingMatrix_map,B]
  have hdegrees := affine_minimal_degrees_field_extension φ (slKirillovMatrix M P i₀)
    (slKirillovMatrix_degreeBound M P i₀ 1
      (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _))
    [Fintype.card m*(q+1)*(q+2)/2-1]
    (generic_divisible_sl_kirillov_minimal_degrees q i₀)
  have hcard : Fintype.card f.Eigenvalues=Fintype.card m*(q+1)*(q+2)/2 := by
    have hp := generic_divisible_gl_jordan_pole_count q hm φ
    convert hp using 1 <;> ring
  have hminimal : HasMinimalKernelDegrees ((E.map C).transpose*J*E.map C)
      [Fintype.card f.Eigenvalues-1] := by
    rw [hres,hcard]
    exact hdegrees
  have hn : ∃ a, c a≠0 ∨ d a≠0 := by
    apply Classical.byContradiction
    intro hzero
    push_neg at hzero
    let v₀ : SLInput (Fin (q+1) × m) m → L := Pi.single (Sum.inl (i₀,i₀)) 1
    have htr : slInputTrace L L (T*ᵥ(S*ᵥv₀))=1 := by
      rw [Matrix.mulVec_mulVec,hTS,Matrix.one_mulVec]
      exact slInputTrace_single L L i₀ 1
    rw [hcoords] at htr
    simp only [(hzero _).1,(hzero _).2,zero_mul,add_zero,Finset.sum_const_zero] at htr
    exact zero_ne_one htr
  refine ⟨T,S,c,d,hTS,hST,hcong,htrace,?_⟩
  exact rankTwo_trace_full_support_of_maximal_index (fun a : f.Eigenvalues => a.val)
    c d (Fintype.card m-2) E F hE hEF hminimal hn

end FD56
