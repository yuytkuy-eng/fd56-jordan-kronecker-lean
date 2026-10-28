/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericNondivisibleLocus
import FD56.Hilbert.KroneckerEndpoints

/-! The common nondivisible GL/SL principal locus consists of independent
ordered coadjoint pairs, with fixed canonical block lists. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Infinite K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_nondivisible_gl_sl_independent_principal_locus
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
          LinearIndependent K ![((fun i j => (M i j).coeff 0),(fun i j => (P i j).coeff 0)),
            ((fun i j => (M i j).coeff 1),(fun i j => (P i j).coeff 1))] ∧
          HasKroneckerDecomposition (glKirillovMatrix M P) gs ∧
          HasKroneckerDecomposition (slKirillovMatrix M P i₀) xs := by
  obtain ⟨gs,xs,hgl,hsl,hgd,hsd,δ,hδ,hpoint,hgood⟩ :=
    generic_nondivisible_gl_sl_nonempty_principal_locus (K:=K) q hq i₀ hlo hhi
  have hlen : gs.length≤Fintype.card n*Fintype.card m := by
    rw [hgl]
    apply Nat.mul_le_mul (Nat.sub_le _ _)
    have he : (q+1)*Fintype.card m=q*Fintype.card m+Fintype.card m := by ring
    omega
  have hpos : 0<gs.sum := by
    have hn : 0<Fintype.card n := by omega
    by_contra hz
    have hs : gs.sum=0 := by omega
    rw [hs] at hgd
    nlinarith
  refine ⟨gs,xs,hgl,hsl,hgd,hsd,δ,hδ,hpoint,?_⟩
  intro x hx
  obtain ⟨hGL,hSL⟩ := hgood x hx
  exact ⟨affine_pair_endpoints_independent_of_positive_kronecker _ _ gs hGL hpos,hGL,hSL⟩

end FD56
