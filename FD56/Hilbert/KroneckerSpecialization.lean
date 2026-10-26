/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialCongruenceSpecialization
import FD56.Hilbert.MixedGLKronecker

/-! Generic constant Kronecker decompositions persist on a nonempty principal parameter locus. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K F σ n : Type*} [Field K] [Field F] [Fintype n] [DecidableEq n]

theorem kroneckerBlockPencil_map (φ : K →+* F) (d : ℕ) :
    (kroneckerBlockPencil (K := K) d).map (Polynomial.mapRingHom φ) =
      kroneckerBlockPencil (K := F) d := by
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [kroneckerBlockPencil,bidiagonalPencil]
  all_goals split_ifs <;> simp

theorem kronecker_decomposition_principal_specialization
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (P : Matrix n n (MvPolynomial σ K)[X]) (xs : List ℕ)
    (h : HasKroneckerDecomposition
      (P.map (Polynomial.mapRingHom (algebraMap (MvPolynomial σ K) F))) xs) :
    ∃ δ : MvPolynomial σ K, δ ≠ 0 ∧
      ∀ x : σ → K, MvPolynomial.eval x δ ≠ 0 →
        HasKroneckerDecomposition (P.map (Polynomial.mapRingHom (MvPolynomial.eval x))) xs := by
  obtain ⟨r,d,hp,T,S,hTS,hST,hform⟩ := h
  let B : Matrix (Σ j, Fin (d j) ⊕ Fin (d j+1))
      (Σ j, Fin (d j) ⊕ Fin (d j+1)) K[X] :=
    Matrix.blockDiagonal' (fun j : Fin r => kroneckerBlockPencil (K := K) (d j))
  have hm : B.map (Polynomial.mapRingHom
      ((algebraMap (MvPolynomial σ K) F).comp MvPolynomial.C)) =
      Matrix.blockDiagonal' (fun j : Fin r => kroneckerBlockPencil (K := F) (d j)) := by
    dsimp only [B]
    rw [Matrix.blockDiagonal'_map _ _ (map_zero _)]
    simp only [kroneckerBlockPencil_map]
  obtain ⟨δ,hδ,he⟩ := polynomial_congruence_principal_specialization P B T S hTS hST
    (hform.trans hm.symm)
  refine ⟨δ,hδ,?_⟩
  intro x hx
  obtain ⟨U,V,hUV,hVU,hcong⟩ := he x hx
  exact ⟨r,d,hp,U,V,hUV,hVU,hcong⟩

theorem kronecker_decomposition_nonempty_principal_locus [Infinite K]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (P : Matrix n n (MvPolynomial σ K)[X]) (xs : List ℕ)
    (h : HasKroneckerDecomposition
      (P.map (Polynomial.mapRingHom (algebraMap (MvPolynomial σ K) F))) xs) :
    ∃ δ : MvPolynomial σ K, δ ≠ 0 ∧ (∃ x : σ → K, MvPolynomial.eval x δ ≠ 0) ∧
      ∀ x : σ → K, MvPolynomial.eval x δ ≠ 0 →
        HasKroneckerDecomposition (P.map (Polynomial.mapRingHom (MvPolynomial.eval x))) xs := by
  obtain ⟨δ,hδ,he⟩ := kronecker_decomposition_principal_specialization P xs h
  exact ⟨δ,hδ,nonzero_polynomial_has_nonzero_evaluation δ hδ,he⟩

end FD56
