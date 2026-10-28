/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericNondivisibleSLStructure
import FD56.Hilbert.GenericKroneckerLocus

/-! Simultaneous GL and SL canonical decompositions on one nonempty principal locus.
The nondivisible theorem fixes the two degree lists throughout this locus,
without claiming explicit formulas for their individual entries. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Infinite K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_gl_sl_kronecker_common_principal_locus
    (i₀ : n) (gs xs : List ℕ)
    (hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs)
    (hSL : HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs) :
    ∃ δ : MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K,
      δ≠0 ∧ (∃ x, MvPolynomial.eval x δ≠0) ∧
      ∀ x, MvPolynomial.eval x δ≠0 →
        let M := (universalAffineSquare K n m).map
          (Polynomial.mapRingHom (MvPolynomial.eval x))
        let P := (universalAffineRows K n m).map
          (Polynomial.mapRingHom (MvPolynomial.eval x))
        HasKroneckerDecomposition (glKirillovMatrix M P) gs ∧
        HasKroneckerDecomposition (slKirillovMatrix M P i₀) xs := by
  obtain ⟨δg,hg,_,hgl⟩ := generic_gl_kronecker_nonempty_principal_locus gs hGL
  obtain ⟨δs,hs,_,hsl⟩ := generic_sl_kronecker_nonempty_principal_locus i₀ xs hSL
  have hδ : δg*δs≠0 := mul_ne_zero hg hs
  refine ⟨δg*δs,hδ,nonzero_polynomial_has_nonzero_evaluation _ hδ,?_⟩
  intro x hx
  have hprod : MvPolynomial.eval x δg * MvPolynomial.eval x δs≠0 := by
    simpa only [map_mul] using hx
  exact ⟨hgl x (mul_ne_zero_iff.mp hprod).1,hsl x (mul_ne_zero_iff.mp hprod).2⟩

theorem generic_nondivisible_gl_sl_nonempty_principal_locus
    (q : ℕ) (hq : 0<q) (i₀ : n)
    (hlo : q*Fintype.card m<Fintype.card n)
    (hhi : Fintype.card n<(q+1)*Fintype.card m) :
    ∃ gs xs : List ℕ,
      gs.length=(Fintype.card n-q*Fintype.card m)*((q+1)*Fintype.card m-Fintype.card n) ∧
      xs.length=gs.length+1 ∧
      2*gs.sum+gs.length=Fintype.card n*(Fintype.card n+Fintype.card m) ∧
      2*xs.sum+xs.length+1=Fintype.card n*(Fintype.card n+Fintype.card m) ∧
      ∃ δ : MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K,
        δ≠0 ∧ (∃ x, MvPolynomial.eval x δ≠0) ∧
        ∀ x, MvPolynomial.eval x δ≠0 →
          let M := (universalAffineSquare K n m).map
            (Polynomial.mapRingHom (MvPolynomial.eval x))
          let P := (universalAffineRows K n m).map
            (Polynomial.mapRingHom (MvPolynomial.eval x))
          HasKroneckerDecomposition (glKirillovMatrix M P) gs ∧
          HasKroneckerDecomposition (slKirillovMatrix M P i₀) xs := by
  obtain ⟨gs,hgl,hgd,_,hGL⟩ :=
    generic_nondivisible_gl_kronecker_structure (K:=K) q hq hlo hhi
  obtain ⟨xs,hsl,hsd,_,hSL⟩ :=
    generic_nondivisible_sl_kronecker_structure (K:=K) q hq i₀ hlo hhi
  exact ⟨gs,xs,hgl,by omega,hgd,hsd,
    generic_gl_sl_kronecker_common_principal_locus i₀ gs xs hGL hSL⟩

end FD56
