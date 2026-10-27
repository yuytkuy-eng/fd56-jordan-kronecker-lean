/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityCertificateSpecialization
import FD56.LinearAlgebra.PolynomialInverseCertificates
import FD56.LinearAlgebra.PolynomialCongruenceSpecialization
import FD56.Stabilizer.GenericDivisibleGLDeterminant
import FD56.Stabilizer.GenericSquareGLJordan

/-! A nonempty principal locus of actual affine pairs satisfies the finite
observability certificates for the divisible regular classification. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} {m : Type} [Field K] [Infinite K] [Fintype m] [DecidableEq m]

private theorem gl_leading_coefficient_map {R S n m : Type*} [CommRing R] [CommRing S]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (φ : R →+* S) (M : Matrix n n R[X]) (P : Matrix m n R[X]) :
    (fun i j => (glKirillovMatrix (M.map (Polynomial.mapRingHom φ))
      (P.map (Polynomial.mapRingHom φ)) i j).coeff 1)=
      Matrix.map (fun i j => (glKirillovMatrix M P i j).coeff 1) φ := by
  rw [← glKirillovMatrix_map]
  funext i j
  simp only [Matrix.map_apply,Polynomial.coe_mapRingHom,Polynomial.coeff_map]

theorem generic_divisible_observability_nonempty_principal_locus
    (q : ℕ) (hm : 2≤Fintype.card m) :
    ∃ δ : MvPolynomial (MatrixParameters (Fin (q+1) × m) m ⊕
      MatrixParameters (Fin (q+1) × m) m) K,
      δ≠0 ∧ (∃ x, MvPolynomial.eval x δ≠0) ∧
      ∀ x, MvPolynomial.eval x δ≠0 →
        let M := (universalAffineSquare K (Fin (q+1) × m) m).map
          (Polynomial.mapRingHom (MvPolynomial.eval x))
        let P := (universalAffineRows K (Fin (q+1) × m) m).map
          (Polynomial.mapRingHom (MvPolynomial.eval x))
        (observabilityMatrix M P (q+1)).det.Separable ∧
          (∃ W : Matrix (Fin (q+1) × m) (Fin q × m) K[X],
            observabilityMatrix M P q*W=1) ∧
          (∃ V : Matrix (Fin (q+1) × m) (Fin (q+2) × m) K[X],
            V*observabilityMatrix M P (q+2)=1) ∧
          Matrix.det (fun i j => (glKirillovMatrix M P i j).coeff 1)≠0 := by
  let R := MvPolynomial (MatrixParameters (Fin (q+1) × m) m ⊕
    MatrixParameters (Fin (q+1) × m) m) K
  let F := AffineCoefficientField K (MatrixParameters (Fin (q+1) × m) m)
  let ι := algebraMap R F
  let M := universalAffineSquare K (Fin (q+1) × m) m
  let P := universalAffineRows K (Fin (q+1) × m) m
  have hwide : q*Fintype.card m<Fintype.card (Fin (q+1) × m) := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    nlinarith
  have htall : Fintype.card (Fin (q+1) × m)<(q+2)*Fintype.card m := by
    simp only [Fintype.card_prod,Fintype.card_fin]
    nlinarith
  obtain ⟨W,hW⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hwide
  obtain ⟨V,hV⟩ := generic_affine_observability_left_inverse (K:=K) (q+2) hm htall
  have hWM : (observabilityMatrix M P q).map (Polynomial.mapRingHom ι)*W=1 := by
    rw [observabilityMatrix_map,universalAffineSquare_generic,universalAffineRows_generic]
    exact hW
  have hVM : V*(observabilityMatrix M P (q+2)).map (Polynomial.mapRingHom ι)=1 := by
    rw [observabilityMatrix_map,universalAffineSquare_generic,universalAffineRows_generic]
    exact hV
  obtain ⟨dW,U,hdW,hU⟩ := polynomial_right_inverse_clear_denominators _ W hWM
  obtain ⟨dV,Z,hdV,hZ⟩ := polynomial_left_inverse_clear_denominators _ V hVM
  have hs : ((observabilityMatrix M P (q+1)).det.map ι).Separable := by
    rw [show (observabilityMatrix M P (q+1)).det.map ι=
      ((observabilityMatrix M P (q+1)).map (Polynomial.mapRingHom ι)).det from
        (Polynomial.mapRingHom ι).map_det _]
    rw [observabilityMatrix_map,universalAffineSquare_generic,universalAffineRows_generic]
    exact (generic_divisible_observability_separable K m (q+1)).2
  obtain ⟨dS,A,B,hdS,hAB⟩ := polynomial_separability_clear_denominators _ hs
  let C₁ : Matrix (SLInput (Fin (q+1) × m) m) (SLInput (Fin (q+1) × m) m) R :=
    fun i j => (glKirillovMatrix M P i j).coeff 1
  have hC : C₁.map ι=(fun i j => (glKirillovMatrix
      (genericAffineSquare K (Fin (q+1) × m) m)
      (genericAffineRows K (Fin (q+1) × m) m) i j).coeff 1) := by
    change Matrix.map (fun i j => (glKirillovMatrix M P i j).coeff 1) ι=_
    rw [← gl_leading_coefficient_map ι M P,universalAffineSquare_generic,universalAffineRows_generic]
  have hdet : C₁.det≠0 := by
    intro hz
    apply generic_divisible_gl_leading_det_ne_zero K m (q+1)
    rw [← hC]
    have he := ι.map_det C₁
    change ι C₁.det=(C₁.map ι).det at he
    exact he.symm.trans (by rw [hz,map_zero])
  let δ : R := dW*dV*dS*C₁.det
  have hδ : δ≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hdW hdV) hdS) hdet
  refine ⟨δ,hδ,nonzero_polynomial_has_nonzero_evaluation δ hδ,?_⟩
  intro x hx
  let ψ : R →+* K := MvPolynomial.eval x
  have hcert : ψ (dW*dV*dS)≠0 := by
    intro hz
    apply hx
    change ψ (dW*dV*dS*C₁.det)=0
    rw [map_mul,hz,zero_mul]
  have hlead : ψ C₁.det≠0 := by
    intro hz
    apply hx
    change ψ (dW*dV*dS*C₁.det)=0
    rw [map_mul,hz,mul_zero]
  obtain ⟨hsep,hR,hL⟩ := divisible_observability_certificate_specialization q M P U Z A B
    dW dV dS hU hZ hAB ψ hcert
  refine ⟨hsep,hR,hL,?_⟩
  rw [gl_leading_coefficient_map]
  change (C₁.map ψ).det≠0
  have he := ψ.map_det C₁
  change ψ C₁.det=(C₁.map ψ).det at he
  intro hz
  exact hlead (he.trans hz)

end FD56
