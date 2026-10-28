/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericObservabilityDegreeBudget
import FD56.Stabilizer.InteriorSelectedMinorFactorization
import FD56.Stabilizer.GenericMinorDifferentialImage
import FD56.LinearAlgebra.PluckerLinearizedRelations

/-! All two-row augmented observability minors and their actual scalar
gradients satisfy the full Plucker tangent equations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

variable (s q : ℕ) [NeZero s]

def twoColumnInteriorRow (ij : Fin (2+s) × Fin (2+s)) : Fin ((2+s)*q+2) → Fin (2+s) :=
  fun k => Sum.elim (fun t : Fin q × Fin (2+s) => t.2) ![ij.1,ij.2]
    (interiorPrefixEquiv 2 s q k)

private theorem twoColumnInteriorLevel_prefix (t : Fin q) (a : Fin (2+s)) :
    interiorLevel 2 s q ((interiorPrefixEquiv 2 s q).symm (Sum.inl (t,a)))=t.val := by
  change ((2+s)*t.val+a.val)/(2+s)=t.val
  rw [Nat.mul_add_div (by omega : 0<2+s),Nat.div_eq_of_lt a.isLt,Nat.add_zero]

theorem twoColumnInteriorRow_lower_closed (ij : Fin (2+s) × Fin (2+s)) :
    ∀ k t, t < interiorLevel 2 s q k → ∀ a, ∃ l,
      interiorLevel 2 s q l=t ∧ twoColumnInteriorRow s q ij l=a := by
  apply interior_lower_closed 2 s q
  intro k hk
  simp only [twoColumnInteriorRow,interiorPrefixEquiv,Equiv.coe_fn_mk,hk,↓reduceDIte,
    Sum.elim_inl,interiorBaseRow]

theorem two_column_selected_matrix_fromRows {R : Type*} [CommRing R]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) R)
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) R) (ij : Fin (2+s) × Fin (2+s)) :
    observabilitySelectedMatrix M P (interiorLevel 2 s q) (twoColumnInteriorRow s q ij)=
      (Matrix.fromRows (observabilityMatrix M P q)
        ((P*M^q).submatrix ![ij.1,ij.2] id)).submatrix (interiorPrefixEquiv 2 s q) id := by
  funext k j
  obtain ⟨w,rfl⟩ := (interiorPrefixEquiv 2 s q).symm.surjective k
  rcases w with ⟨t,a⟩|a
  · simp only [observabilitySelectedMatrix,twoColumnInteriorRow,Equiv.apply_symm_apply,
      Sum.elim_inl,twoColumnInteriorLevel_prefix,Matrix.submatrix_apply,
      Matrix.fromRows_apply_inl,observabilityMatrix,id_eq]
  · simp only [observabilitySelectedMatrix,twoColumnInteriorRow,Equiv.apply_symm_apply,
      Sum.elim_inr,interiorPrefixEquiv_symm_inr,interiorLevel_missing,interiorPrefixEquiv_missing,
      Matrix.submatrix_apply,Matrix.fromRows_apply_inr,id_eq]

def twoColumnInteriorMinors {R : Type*} [CommRing R]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) R)
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) R) : Matrix (Fin (2+s)) (Fin (2+s)) R :=
  fun i j => (observabilitySelectedMatrix M P (interiorLevel 2 s q)
    (twoColumnInteriorRow s q (i,j))).det

def twoColumnInteriorScalarGradients {R : Type*} [CommRing R]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) R)
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) R) :
    Matrix (SLInput (Fin ((2+s)*q+2)) (Fin (2+s))) (Fin (2+s) × Fin (2+s)) R :=
  fun k ij => observabilityScalarLift M P (interiorLevel 2 s q) (twoColumnInteriorRow s q ij) k

theorem twoColumnInteriorScalarGradients_kernel {K : Type*} [Field K]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) K[X])
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) K[X]) (i₀ : Fin ((2+s)*q+2)) :
    slEquationMatrix M P i₀*twoColumnInteriorScalarGradients s q M P=0 := by
  funext k ij
  exact congrFun (observabilityScalarLift_sl_kernel M P (interiorLevel 2 s q)
    (twoColumnInteriorRow s q ij) (twoColumnInteriorRow_lower_closed s q ij) i₀) k

private theorem plucker_pair_wedge {R m : Type*} [CommRing R]
    (G : Matrix m (Fin 2) R) (i j : m) :
    pluckerMinorVector G ![i,j]=twoColumnWedge (fun k => G k 0) (fun k => G k 1) i j := by
  simp only [pluckerMinorVector,Matrix.det_fin_two,Matrix.submatrix_apply,id_eq,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,twoColumnWedge]
  ring

theorem twoColumnInteriorMinors_common_scalar {K : Type*} [Field K]
    (M : Matrix (Fin ((2+s)*q+2)) (Fin ((2+s)*q+2)) K[X])
    (P : Matrix (Fin (2+s)) (Fin ((2+s)*q+2)) K[X])
    (R : Matrix (Fin ((2+s)*q+2)) (Fin q × Fin (2+s)) K[X])
    (hR : observabilityMatrix M P q*R=1)
    (B : Basis (Fin 2) K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) :
    ∃ c : K, c≠0 ∧ twoColumnInteriorMinors s q M P=C c • twoColumnWedge
      (fun i => (P*M^q*polynomialKernelBasisMatrix _ B) i 0)
      (fun i => (P*M^q*polynomialKernelBasisMatrix _ B) i 1) := by
  obtain ⟨c,hc,h⟩ := selected_augmented_minors_common_scalar_equiv
    (interiorPrefixEquiv 2 s q) (observabilityMatrix M P q) R hR B (P*M^q)
  refine ⟨c,hc,?_⟩
  funext i j
  have hh := h ![i,j]
  change _=C c*pluckerMinorVector
    (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B) ![i,j] at hh
  rw [plucker_pair_wedge] at hh
  simpa only [twoColumnInteriorMinors,two_column_selected_matrix_fromRows,
    Pi.smul_apply,smul_eq_mul] using hh

variable {K : Type*} [Field K]

def genericTwoColumnInteriorMinors := twoColumnInteriorMinors s q
  (genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s)))
  (genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s)))

def genericTwoColumnInteriorScalarGradients := twoColumnInteriorScalarGradients s q
  (genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s)))
  (genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s)))

theorem generic_two_column_minors_plucker_relation (i j k l : Fin (2+s)) :
    pluckerQuadraticRelation (genericTwoColumnInteriorMinors (K:=K) s q) i j k l=0 := by
  let M := genericAffineSquare K (Fin ((2+s)*q+2)) (Fin (2+s))
  let P := genericAffineRows K (Fin ((2+s)*q+2)) (Fin (2+s))
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin (2+s))<Fintype.card (Fin ((2+s)*q+2)) := by
    simp only [Fintype.card_fin]; nlinarith
  obtain ⟨r,B,e,hV,hVL,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have hmin : HasMinimalKernelDegrees O (List.ofFn e) := ⟨r,B,e,hV,hVL,List.Perm.refl _⟩
  have hr := (generic_observability_kernel_degree_budget (K:=K) q hlo _ hmin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hr
  have hr' : r=2 := by nlinarith
  subst r
  obtain ⟨R,hR⟩ := generic_affine_wide_observability_right_inverse (K:=K) q hlo
  obtain ⟨c,_,hc⟩ := twoColumnInteriorMinors_common_scalar s q M P R hR B
  change pluckerQuadraticRelation (twoColumnInteriorMinors s q M P) i j k l=0
  rw [hc]
  exact scaled_wedge_plucker_relation _ _ _ i j k l

theorem generic_two_column_gradient_plucker_relation
    (t : SLInput (Fin ((2+s)*q+2)) (Fin (2+s))) (i j k l : Fin (2+s)) :
    pluckerLinearizedRelation (genericTwoColumnInteriorMinors (K:=K) s q)
      (fun a b => genericTwoColumnInteriorScalarGradients (K:=K) s q t (a,b)) i j k l=0 := by
  classical
  let L := AffineCoefficientField K (MatrixParameters (Fin ((2+s)*q+2)) (Fin (2+s)))
  obtain ⟨D,hD⟩ := generic_minor_derivation_realizes_affine_pairing (K:=K)
    (fun _ : Fin (2+s) × Fin (2+s) => interiorLevel 2 s q)
    (twoColumnInteriorRow s q) (Pi.single t (1:L)) 0
  have he (a b : Fin (2+s)) : polynomialCoefficientDerivation D
      (genericTwoColumnInteriorMinors (K:=K) s q a b)=
        genericTwoColumnInteriorScalarGradients (K:=K) s q t (a,b) := by
    have h := hD (a,b)
    simpa [genericTwoColumnInteriorMinors,twoColumnInteriorMinors,
      genericTwoColumnInteriorScalarGradients,twoColumnInteriorScalarGradients,
      Pi.single_apply,dotProduct] using h
  have h := plucker_relation_coefficient_derivation D
    (genericTwoColumnInteriorMinors (K:=K) s q)
    (generic_two_column_minors_plucker_relation s q) i j k l
  simpa only [he] using h

end FD56
