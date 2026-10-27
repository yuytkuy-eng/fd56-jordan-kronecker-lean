/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleGLJordan
import FD56.Stabilizer.GenericDivisibleGLTrace
import FD56.Hilbert.RankTwoJordanTraceSupport
import FD56.LinearAlgebra.PolynomialCongruenceKernel

/-! The actual trace has two possible coordinates at each pole of a divisible GL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K L : Type*} {m : Type} [Field K] [Field L] [IsAlgClosed L]
  [Fintype m] [DecidableEq m]

local instance genericDivisibleGLTraceSupportDecidableEq : DecidableEq L := Classical.decEq L

theorem generic_divisible_gl_jordan_trace_support (q : ℕ) (hm : 2≤Fintype.card m)
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
      ∀ v, slInputTrace L L (T *ᵥ v)=∑ a : f.Eigenvalues,
        (c a*v ⟨a,Sum.inl (Sum.inl 0)⟩+d a*v ⟨a,Sum.inl (Sum.inr 1)⟩) := by
  classical
  let H₀ := glKirillovMatrix (genericAffineSquare K (Fin (q+1) × m) m)
    (genericAffineRows K (Fin (q+1) × m) m)
  let H := H₀.map (Polynomial.mapRingHom φ)
  let f := polynomialPencilOperator H
  let J := Matrix.blockDiagonal' (fun a : f.Eigenvalues =>
    rankTwoJordanPencil a.val (Fintype.card m-2))
  obtain ⟨T,S,hTS,hST,hcong⟩ := generic_divisible_gl_jordan_decomposition q hm φ
  let ell : ((Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2)) → L) →ₗ[L] L :=
    (slInputTrace L L).comp (Matrix.toLin' T)
  have hell : ∀ a : f.Eigenvalues, ∀ v,
      J.map (Polynomial.evalRingHom a.val) *ᵥ v=0 → ell v=0 := by
    intro a v hv
    apply polynomial_congruence_kernel_functional H J T S hTS hcong (slInputTrace L L) a.val _ v hv
    intro z hz
    apply generic_divisible_gl_kernel_trace_zero q hm φ a.val z
    have heval : H.map (Polynomial.evalRingHom a.val)=H₀.map (Polynomial.eval₂RingHom φ a.val) := by
      funext i j
      simp [H,Matrix.map_apply,Polynomial.eval_map]
    rwa [← heval]
  refine ⟨T,S,(fun a => ell (Pi.single ⟨a,Sum.inl (Sum.inl 0)⟩ 1)),
    (fun a => ell (Pi.single ⟨a,Sum.inl (Sum.inr 1)⟩ 1)),hTS,hST,hcong,?_⟩
  intro v
  exact rank_two_jordan_sum_functional_sparse (fun a : f.Eigenvalues => a.val)
    (Fintype.card m-2) ell hell v

end FD56
