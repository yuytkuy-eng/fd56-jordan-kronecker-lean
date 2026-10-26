/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.SLKirillovPencil

/-! Transfer a trace-preserving constant congruence to the actual traceless chart. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m a r : Type*} [Field K] [Fintype n] [Fintype m]
  [Fintype a] [Fintype r] [DecidableEq n] [DecidableEq m]
  [DecidableEq a] [DecidableEq r]

theorem slTraceTransport (i₀ : n)
    (G : Matrix (SLInput n m) a K) (H : Matrix a (SLInput n m) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (ell : (a → K) → K) (htrace : ∀ v, slInputTrace K K (G*ᵥv)=ell v)
    (E : Matrix a r K) (F : Matrix r a K) (hFE : F*E=1)
    (hE : ∀ v, ell (E*ᵥv)=0) (hEF : ∀ v, ell v=0 → E*ᵥ(F*ᵥv)=v) :
    ∃ T : Matrix (SLChartInput n m i₀) r K,
    ∃ S : Matrix r (SLChartInput n m i₀) K,
      T*S=1 ∧ S*T=1 ∧ slChartEmbeddingMatrix i₀*T=G*E := by
  let B : Matrix (SLInput n m) (SLChartInput n m i₀) K := slChartEmbeddingMatrix i₀
  let R : Matrix (SLChartInput n m i₀) (SLInput n m) K := slChartRetractionMatrix i₀
  have hBR (v : r → K) : B*ᵥ(R*ᵥ(G*ᵥ(E*ᵥv)))=G*ᵥ(E*ᵥv) := by
    change slChartEmbeddingMatrix i₀*ᵥ(slChartRetractionMatrix i₀*ᵥ(G*ᵥ(E*ᵥv)))=_
    rw [slChartRetractionMatrix_mulVec,slChartEmbeddingMatrix_mulVec]
    apply slChartEmbed_retract
    rw [htrace,hE]
  have hEFHB (v : SLChartInput n m i₀ → K) : E*ᵥ(F*ᵥ(H*ᵥ(B*ᵥv)))=H*ᵥ(B*ᵥv) := by
    apply hEF
    rw [← htrace,Matrix.mulVec_mulVec,hGH,Matrix.one_mulVec]
    change slInputTrace K K (slChartEmbeddingMatrix i₀*ᵥv)=0
    rw [slChartEmbeddingMatrix_mulVec,slChartEmbed_trace]
  refine ⟨R*G*E,F*H*B,?_,?_,?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change ((R*G*E)*(F*H*B))*ᵥv=(1 : Matrix _ _ K)*ᵥv
    simp only [← Matrix.mulVec_mulVec,Matrix.one_mulVec]
    rw [hEFHB,Matrix.mulVec_mulVec _ G H,hGH,Matrix.one_mulVec]
    change slChartRetractionMatrix i₀*ᵥ(slChartEmbeddingMatrix i₀*ᵥv)=v
    rw [slChartEmbeddingMatrix_mulVec,slChartRetractionMatrix_mulVec,slChartRetract_embed]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change ((F*H*B)*(R*G*E))*ᵥv=(1 : Matrix _ _ K)*ᵥv
    simp only [← Matrix.mulVec_mulVec,Matrix.one_mulVec]
    rw [hBR,Matrix.mulVec_mulVec _ H G,hHG,Matrix.one_mulVec,
      Matrix.mulVec_mulVec _ F E,hFE,Matrix.one_mulVec]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    change (B*(R*G*E))*ᵥv=(G*E)*ᵥv
    simpa only [← Matrix.mulVec_mulVec] using hBR v

theorem slTraceTransport_congruence (i₀ : n)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (A : Matrix a a K[X])
    (G : Matrix (SLInput n m) a K) (H : Matrix a (SLInput n m) K)
    (hGH : G*H=1) (hHG : H*G=1)
    (hcong : (G.map C).transpose*glKirillovMatrix M P*G.map C=A)
    (ell : (a → K) → K) (htrace : ∀ v, slInputTrace K K (G*ᵥv)=ell v)
    (E : Matrix a r K) (F : Matrix r a K) (hFE : F*E=1)
    (hE : ∀ v, ell (E*ᵥv)=0) (hEF : ∀ v, ell v=0 → E*ᵥ(F*ᵥv)=v) :
    ∃ T : Matrix (SLChartInput n m i₀) r K,
    ∃ S : Matrix r (SLChartInput n m i₀) K,
      T*S=1 ∧ S*T=1 ∧
      (T.map C).transpose*slKirillovMatrix M P i₀*T.map C=(E.map C).transpose*A*E.map C := by
  obtain ⟨T,S,hTS,hST,hBT⟩ := slTraceTransport i₀ G H hGH hHG ell htrace E F hFE hE hEF
  refine ⟨T,S,hTS,hST,?_⟩
  have hBTC : slChartEmbeddingMatrix i₀*T.map C=G.map C*E.map C := by
    have h := congrArg (fun Z : Matrix (SLInput n m) r K => Z.map C) hBT
    simpa only [Matrix.map_mul,slChartEmbeddingMatrix_map] using h
  let BC : Matrix (SLInput n m) (SLChartInput n m i₀) K[X] := slChartEmbeddingMatrix i₀
  calc
    _ = (BC*T.map C).transpose*glKirillovMatrix M P*(BC*T.map C) := by
      dsimp only [BC]
      simp only [slKirillovMatrix,Matrix.transpose_mul,Matrix.mul_assoc]
    _ = _ := by
      dsimp only [BC]
      rw [hBTC,Matrix.transpose_mul]
      simpa only [Matrix.mul_assoc] using congrArg
        (fun Z => (E.map C).transpose*Z*E.map C) hcong

end FD56
