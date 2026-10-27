/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RankTwoSLTracedJordan
import FD56.Hilbert.RankTwoJordanTraceSupport
import FD56.Hilbert.RankTwoTraceCovectorCoordinates
import FD56.LinearAlgebra.PolynomialCongruenceKernel

/-! The SL canonical form follows from regular GL blocks, kernel traces, and a maximal minimal index. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m ι : Type*} [Field K] [Fintype n] [Fintype m] [Fintype ι]
  [DecidableEq n] [DecidableEq m] [DecidableEq ι] [Nontrivial ι]

theorem sl_canonical_of_rank_two_gl_and_maximal_index
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (i₀ : n)
    (lam : ι → K) (hlam : Function.Injective lam) (k : ℕ) (a₀ : ι)
    (T : Matrix (SLInput n m) (Σ _ : ι, rankTwoJordanIndex k) K)
    (S : Matrix (Σ _ : ι, rankTwoJordanIndex k) (SLInput n m) K)
    (hTS : T*S=1) (hST : S*T=1)
    (hcong : (T.map C).transpose*glKirillovMatrix M P*T.map C=
      Matrix.blockDiagonal' (fun a => rankTwoJordanPencil (lam a) k))
    (hker : ∀ a v, (glKirillovMatrix M P).map (Polynomial.evalRingHom (lam a)) *ᵥ v=0 →
      slInputTrace K K v=0)
    (hmin : HasMinimalKernelDegrees (slKirillovMatrix M P i₀) [Fintype.card ι-1]) :
    ∃ G : Matrix (SLChartInput n m i₀) (rankTwoSLCanonicalIndex (fun _ : ι => k)) K,
    ∃ J : Matrix (rankTwoSLCanonicalIndex (fun _ : ι => k)) (SLChartInput n m i₀) K,
      G*J=1 ∧ J*G=1 ∧ (G.map C).transpose*slKirillovMatrix M P i₀*G.map C=
        rankTwoSLCanonicalTarget lam (fun _ => k) := by
  classical
  let H := glKirillovMatrix M P
  let J := Matrix.blockDiagonal' (fun a => rankTwoJordanPencil (lam a) k)
  let ell : ((Σ _ : ι, rankTwoJordanIndex k) → K) →ₗ[K] K :=
    (slInputTrace K K).comp (Matrix.toLin' T)
  have hell : ∀ a : ι, ∀ v, J.map (Polynomial.evalRingHom (lam a)) *ᵥ v=0 → ell v=0 := by
    intro a v hv
    exact polynomial_congruence_kernel_functional H J T S hTS hcong
      (slInputTrace K K) (lam a) (hker a) v hv
  let c : ι → K := fun a => ell (Pi.single ⟨a,.inl (.inl 0)⟩ 1)
  let d : ι → K := fun a => ell (Pi.single ⟨a,.inl (.inr 1)⟩ 1)
  have hcoords (v) : slInputTrace K K (T*ᵥv)=∑ a : ι,
      (c a*v ⟨a,.inl (.inl 0)⟩+d a*v ⟨a,.inl (.inr 1)⟩) :=
    rank_two_jordan_sum_functional_sparse lam k ell hell v
  let cv := rankTwoTraceSumCovector c d k
  have htrace (v) : slInputTrace K K (T*ᵥv)=cv ⬝ᵥ v := by
    rw [hcoords,rankTwoTraceSumCovector_dotProduct]
  let B : Matrix (SLInput n m) (SLChartInput n m i₀) K := slChartEmbeddingMatrix i₀
  let R : Matrix (SLChartInput n m i₀) (SLInput n m) K := slChartRetractionMatrix i₀
  let E := S*B
  let F := R*T
  have hTE : T*E=B := by simp only [E,← Matrix.mul_assoc,hTS,Matrix.one_mul]
  have hEtrace (v) : cv ⬝ᵥ (E*ᵥv)=0 := by
    rw [← htrace,Matrix.mulVec_mulVec,hTE]
    change slInputTrace K K (slChartEmbeddingMatrix i₀*ᵥv)=0
    rw [slChartEmbeddingMatrix_mulVec,slChartEmbed_trace]
  have hE : E.transpose*ᵥcv=0 := by
    funext j
    have hz := hEtrace (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at hz
    simpa only [dotProduct,Matrix.mulVec,Matrix.transpose_apply,Pi.zero_apply,mul_comm] using hz
  have hEF : ∀ v, cv ⬝ᵥ v=0 → E*ᵥ(F*ᵥv)=v := by
    intro v hv
    have ht : slInputTrace K K (T*ᵥv)=0 := (htrace v).trans hv
    have hrec : B*ᵥ(R*ᵥ(T*ᵥv))=T*ᵥv := by
      change slChartEmbeddingMatrix i₀*ᵥ(slChartRetractionMatrix i₀*ᵥ(T*ᵥv))=T*ᵥv
      rw [slChartRetractionMatrix_mulVec,slChartEmbeddingMatrix_mulVec]
      exact slChartEmbed_retract K K i₀ (T*ᵥv) ht
    simp only [E,F,← Matrix.mulVec_mulVec]
    rw [hrec,Matrix.mulVec_mulVec,hST,Matrix.one_mulVec]
  have hEC : T.map C*E.map C=B.map C := by rw [← Matrix.map_mul,hTE]
  have hcongJ : (T.map C).transpose*H*T.map C=J := hcong
  have hres : (E.map C).transpose*J*E.map C=slKirillovMatrix M P i₀ := by
    calc
      _ = (B.map C).transpose*H*B.map C := by
        rw [← hcongJ]
        calc
          _ = (T.map C*E.map C).transpose*H*(T.map C*E.map C) := by
            simp only [Matrix.transpose_mul,Matrix.mul_assoc]
          _ = _ := by rw [hEC]
      _ = _ := by simp only [B,H,slChartEmbeddingMatrix_map,slKirillovMatrix]
  have hminimal : HasMinimalKernelDegrees ((E.map C).transpose*J*E.map C)
      [Fintype.card ι-1] := by rw [hres]; exact hmin
  have hn : ∃ a, c a≠0 ∨ d a≠0 := by
    apply Classical.byContradiction
    intro hzero
    push_neg at hzero
    let v₀ : SLInput n m → K := Pi.single (Sum.inl (i₀,i₀)) 1
    have htr : slInputTrace K K (T*ᵥ(S*ᵥv₀))=1 := by
      rw [Matrix.mulVec_mulVec,hTS,Matrix.one_mulVec]
      exact slInputTrace_single K K i₀ 1
    rw [hcoords] at htr
    simp only [(hzero _).1,(hzero _).2,zero_mul,add_zero,Finset.sum_const_zero] at htr
    exact zero_ne_one htr
  have hab := rankTwo_trace_full_support_of_maximal_index lam c d k E F hE hEF hminimal hn
  exact rankTwoSL_canonical_of_sparse_trace M P i₀ lam hlam (fun _ => k) a₀
    T S hTS hST hcong c d hab hcoords

end FD56
