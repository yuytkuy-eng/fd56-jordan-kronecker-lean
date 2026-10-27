/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDivisibleObservabilityLocus
import FD56.Stabilizer.DivisibleSLJordanCriterion
import FD56.Stabilizer.KirillovParameterMap

/-! Full GL and SL canonical decompositions at every point of a nonempty
principal locus in the original affine-pair parameter space. -/

noncomputable section
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
namespace FD56
open Matrix Polynomial
variable {K : Type*} {m : Type} [Field K] [IsAlgClosed K]
  [Infinite K] [Fintype m] [DecidableEq m]
local instance genericDivisibleCanonicalLocusDecidableEq : DecidableEq K := Classical.decEq K

private theorem affine_pencil_map_degree {R a b : Type*} [CommRing R]
    (A B : Matrix a b R) (φ : R →+* K) :
    DegreeBound ((affineMatrixPencil A B).map (Polynomial.mapRingHom φ)) 1 := by
  intro i j
  simpa only [Matrix.map_apply,affineMatrixPencil,Polynomial.coe_mapRingHom,
    Polynomial.map_add,Polynomial.map_C,Polynomial.map_mul,Polynomial.map_X]
    using affineMatrixPencil_degree (A.map φ) (B.map φ) i j

theorem generic_divisible_gl_sl_canonical_nonempty_principal_locus
    (q : ℕ) (i₀ : Fin (q+1) × m) (hm : 2≤Fintype.card m) :
    ∃ δ : MvPolynomial (MatrixParameters (Fin (q+1) × m) m ⊕
      MatrixParameters (Fin (q+1) × m) m) K,
      δ≠0 ∧ (∃ x, MvPolynomial.eval x δ≠0) ∧
      ∀ x, MvPolynomial.eval x δ≠0 →
        let M := (universalAffineSquare K (Fin (q+1) × m) m).map
          (Polynomial.mapRingHom (MvPolynomial.eval x))
        let P := (universalAffineRows K (Fin (q+1) × m) m).map
          (Polynomial.mapRingHom (MvPolynomial.eval x))
        let H := glKirillovMatrix M P
        let f := polynomialPencilOperator H
        Fintype.card f.Eigenvalues=Fintype.card m*(q+1)*(q+2)/2 ∧
        LinearIndependent K
          ![((fun i j => (M i j).coeff 0),(fun i j => (P i j).coeff 0)),
            ((fun i j => (M i j).coeff 1),(fun i j => (P i j).coeff 1))] ∧
        (∃ T : Matrix (SLInput (Fin (q+1) × m) m)
          (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2)) K,
         ∃ S : Matrix (Σ _ : f.Eigenvalues, rankTwoJordanIndex (Fintype.card m-2))
          (SLInput (Fin (q+1) × m) m) K,
          T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*H*T.map C=
            Matrix.blockDiagonal' (fun a : f.Eigenvalues =>
              rankTwoJordanPencil a.val (Fintype.card m-2))) ∧
        (∃ T : Matrix (SLChartInput (Fin (q+1) × m) m i₀)
          (rankTwoSLCanonicalIndex (fun _ : f.Eigenvalues => Fintype.card m-2)) K,
         ∃ S : Matrix (rankTwoSLCanonicalIndex (fun _ : f.Eigenvalues => Fintype.card m-2))
          (SLChartInput (Fin (q+1) × m) m i₀) K,
          T*S=1 ∧ S*T=1 ∧ (T.map C).transpose*slKirillovMatrix M P i₀*T.map C=
            rankTwoSLCanonicalTarget (fun a : f.Eigenvalues => a.val)
              (fun _ => Fintype.card m-2)) := by
  classical
  obtain ⟨δ,hδ,hpoint,hgood⟩ :=
    generic_divisible_observability_nonempty_principal_locus (K:=K) q hm
  refine ⟨δ,hδ,hpoint,?_⟩
  intro x hx
  let M := (universalAffineSquare K (Fin (q+1) × m) m).map
    (Polynomial.mapRingHom (MvPolynomial.eval x))
  let P := (universalAffineRows K (Fin (q+1) × m) m).map
    (Polynomial.mapRingHom (MvPolynomial.eval x))
  obtain ⟨hs,⟨R,hR⟩,⟨V,hV⟩,hlead⟩ := hgood x hx
  have hM : DegreeBound M 1 := affine_pencil_map_degree _ _ _
  have hP : DegreeBound P 1 := affine_pencil_map_degree _ _ _
  obtain ⟨T,S,hTS,hST,hcong⟩ :=
    divisible_gl_jordan_of_observability_inverses q M P hm hM hP R V hR hV hs hlead
  let H := glKirillovMatrix M P
  let f := polynomialPencilOperator H
  have hcount : Fintype.card f.Eigenvalues=Fintype.card m*(q+1)*(q+2)/2 :=
    divisible_rank_two_basis_pole_count q hm T S hTS hST
  have hprod : 2*Fintype.card m≤Fintype.card m*(q+1)*(q+2) := by
    have : 2≤(q+1)*(q+2) := by nlinarith
    nlinarith
  letI : Nontrivial f.Eigenvalues := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nonempty (SLInput (Fin (q+1) × m) m) := ⟨Sum.inl (i₀,i₀)⟩
  obtain ⟨a,b,hab⟩ := exists_pair_ne f.Eigenvalues
  have hind := polynomial_pencil_endpoints_independent_of_two_eigenvalues H
    (glKirillovMatrix_degreeBound M P 1 hM hP) hlead a b hab
  refine ⟨hcount,affine_pair_endpoints_independent_of_kirillov M P hind,
    ⟨T,S,hTS,hST,hcong⟩,?_⟩
  exact divisible_sl_jordan_of_observability_inverses q M P i₀ hm hM hP R V hR hV hs hlead

end FD56
