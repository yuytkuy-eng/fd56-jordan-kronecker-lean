/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDimension
import FD56.Stabilizer.FieldSLMatrix
import FD56.Stabilizer.PolynomialSLScalar
import Mathlib.Algebra.MvPolynomial.Rename

/-! Generic affine pencils have the proved generic radical dimensions.
Specialization at parameter zero proves that the substitution is injective. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def AffineCoefficientField (K σ : Type*) [CommRing K] :=
  FractionRing (MvPolynomial (σ ⊕ σ) K)

instance (K σ : Type*) [Field K] : Field (AffineCoefficientField K σ) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (σ ⊕ σ) K)))

instance (K σ : Type*) [Field K] : Algebra (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ) :=
  inferInstanceAs (Algebra _ (FractionRing (MvPolynomial (σ ⊕ σ) K)))

instance (K σ : Type*) [Field K] : IsFractionRing (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ) :=
  inferInstanceAs (IsFractionRing _ (FractionRing (MvPolynomial (σ ⊕ σ) K)))

def affineParameterMap (K σ : Type*) [Field K] :
    MvPolynomial σ K →+* (AffineCoefficientField K σ)[X] :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp ((algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)).comp MvPolynomial.C))
    (fun i => Polynomial.C (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)
        (MvPolynomial.X (Sum.inl i))) +
      Polynomial.X * Polynomial.C (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)
        (MvPolynomial.X (Sum.inr i))))

theorem affineParameterMap_degree (K σ : Type*) [Field K] (i : σ) :
    ((affineParameterMap K σ) (MvPolynomial.X i)).natDegree ≤ 1 := by
  simp only [affineParameterMap, MvPolynomial.eval₂Hom_X']
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact Polynomial.natDegree_mul_le.trans (by simp)

theorem affineParameterMap_zero (K σ : Type*) [Field K] :
    (Polynomial.evalRingHom (0 : AffineCoefficientField K σ)).comp (affineParameterMap K σ) =
      (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)).comp
        (MvPolynomial.rename (Sum.inl : σ → σ ⊕ σ)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [affineParameterMap]
  · intro i
    simp [affineParameterMap]

theorem affineParameterMap_injective (K σ : Type*) [Field K] :
    Function.Injective (affineParameterMap K σ) := by
  have h : Function.Injective
      ((Polynomial.evalRingHom (0 : AffineCoefficientField K σ)).comp (affineParameterMap K σ)) := by
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)).comp
      (MvPolynomial.rename_injective (R := K) (Sum.inl : σ → σ ⊕ σ) Sum.inl_injective)
  intro f g hfg
  apply h
  exact congrArg (Polynomial.evalRingHom 0) hfg

def GenericPencilField (K n m : Type*) [Field K] :=
  FractionRing ((AffineCoefficientField K (MatrixParameters n m))[X])

instance (K n m : Type*) [Field K] : Field (GenericPencilField K n m) :=
  inferInstanceAs (Field (FractionRing ((AffineCoefficientField K (MatrixParameters n m))[X])))

instance (K n m : Type*) [Field K] :
    Algebra ((AffineCoefficientField K (MatrixParameters n m))[X]) (GenericPencilField K n m) :=
  inferInstanceAs (Algebra _ (FractionRing ((AffineCoefficientField K (MatrixParameters n m))[X])))

instance (K n m : Type*) [Field K] :
    IsFractionRing ((AffineCoefficientField K (MatrixParameters n m))[X]) (GenericPencilField K n m) :=
  inferInstanceAs (IsFractionRing _ (FractionRing ((AffineCoefficientField K (MatrixParameters n m))[X])))

def genericAffineSquare (K n m : Type*) [Field K] :
    Matrix n n ((AffineCoefficientField K (MatrixParameters n m))[X]) :=
  (universalSquare K n m).map (affineParameterMap K (MatrixParameters n m))

def genericAffineRows (K n m : Type*) [Field K] :
    Matrix m n ((AffineCoefficientField K (MatrixParameters n m))[X]) :=
  (universalRows K n m).map (affineParameterMap K (MatrixParameters n m))

def genericPencilSquare (K n m : Type*) [Field K] : Matrix n n (GenericPencilField K n m) :=
  (genericAffineSquare K n m).map (algebraMap ((AffineCoefficientField K (MatrixParameters n m))[X]) _)

theorem genericAffineSquare_degree (K n m : Type*) [Field K] (i j : n) :
    (genericAffineSquare K n m i j).natDegree ≤ 1 :=
  affineParameterMap_degree K _ _

theorem genericAffineRows_degree (K n m : Type*) [Field K] (i : m) (j : n) :
    (genericAffineRows K n m i j).natDegree ≤ 1 :=
  affineParameterMap_degree K _ _

def genericPencilRows (K n m : Type*) [Field K] : Matrix m n (GenericPencilField K n m) :=
  (genericAffineRows K n m).map (algebraMap ((AffineCoefficientField K (MatrixParameters n m))[X]) _)

theorem generic_pencil_radical_dimensions {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ) :
    Module.finrank (GenericPencilField K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (glStabilizerSpace (genericPencilSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericPencilRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))) =
        Fintype.card r * Fintype.card s ∧
    Module.finrank (GenericPencilField K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (fieldSLRadical (genericPencilSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericPencilRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))) =
        Fintype.card r * Fintype.card s + 1 := by
  exact universal_radical_dimensions q
    ((algebraMap _ _).comp (affineParameterMap K _))
    ((IsFractionRing.injective _ _).comp (affineParameterMap_injective K _))

theorem generic_pencil_radical_dimensions_tall {K : Type*} {n s : Type} [Field K]
    [Fintype n] [Fintype s] [DecidableEq n] [Nonempty n] :
    Module.finrank (GenericPencilField K n (n ⊕ s))
      (glStabilizerSpace (genericPencilSquare K n (n ⊕ s)) (genericPencilRows K n (n ⊕ s))) =
        Fintype.card n * Fintype.card s ∧
    Module.finrank (GenericPencilField K n (n ⊕ s))
      (fieldSLRadical (genericPencilSquare K n (n ⊕ s)) (genericPencilRows K n (n ⊕ s))) =
        Fintype.card n * Fintype.card s + 1 := by
  exact universal_radical_dimensions_tall
    ((algebraMap _ _).comp (affineParameterMap K _))
    ((IsFractionRing.injective _ _).comp (affineParameterMap_injective K _))

theorem generic_pencil_scalar_one {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ)
    [DecidableEq (blockIndex (r ⊕ s) r (q + 1))] [DecidableEq (r ⊕ s)] :
    ∃ z ∈ fieldSLRadical (genericPencilSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (genericPencilRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)),
      stabilizerResidual (genericPencilSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericPencilRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) z = 1 := by
  letI : Nonempty (blockIndex (r ⊕ s) r (q + 1)) :=
    inferInstanceAs (Nonempty ((r ⊕ s) ⊕ blockIndex (r ⊕ s) r q))
  apply exists_fieldSL_scalar_one_of_finrank _ _ (Classical.choice inferInstance)
  obtain ⟨hg, hs⟩ := generic_pencil_radical_dimensions (K := K) (r := r) (s := s) q
  exact lt_of_eq_of_lt hg (lt_of_lt_of_eq (Nat.lt_succ_self _) hs.symm)

theorem generic_affine_polynomial_scalar {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ)
    [DecidableEq (blockIndex (r ⊕ s) r (q + 1))] [DecidableEq (r ⊕ s)]
    (i₀ : blockIndex (r ⊕ s) r (q + 1)) :
    ∃ X U, ∃ c : (AffineCoefficientField K
      (MatrixParameters (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)))[X],
      c ≠ 0 ∧ SLRadical
        (genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) X U ∧
      stabilizerResidual (genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) (X, U) = c • 1 := by
  obtain ⟨z, hz, hu⟩ := generic_pencil_scalar_one (K := K) (r := r) (s := s) q
  exact polynomial_sl_scalar_nonzero _ _ i₀ z hz hu

theorem generic_pencil_sl_matrix_nullity {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ)
    [DecidableEq (blockIndex (r ⊕ s) r (q + 1))] [DecidableEq (r ⊕ s)]
    (i₀ : blockIndex (r ⊕ s) r (q + 1)) :
    Module.finrank (GenericPencilField K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix
        (genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) i₀).map
          (algebraMap _ (GenericPencilField K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)))))) = Fintype.card r * Fintype.card s + 1 := by
  rw [slEquationMatrix_specialized_finrank]
  exact (generic_pencil_radical_dimensions (K := K) (r := r) (s := s) q).2

theorem generic_affine_gl_radical_finrank_extension {K F : Type*} {r s : Type}
    [Field K] [Field F] [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ)
    (ψ : (AffineCoefficientField K (MatrixParameters (blockIndex (r ⊕ s) r (q + 1))
      (r ⊕ s)))[X] →+* F) (hψ : Function.Injective ψ) :
    Module.finrank F (glStabilizerSpace
      ((genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)).map ψ)
      ((genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)).map ψ)) =
        Fintype.card r * Fintype.card s :=
  (universal_radical_dimensions q (ψ.comp (affineParameterMap K _))
    (hψ.comp (affineParameterMap_injective K _))).1

theorem generic_affine_sl_matrix_nullity_extension {K F : Type*} {r s : Type}
    [Field K] [Field F] [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ)
    [DecidableEq (blockIndex (r ⊕ s) r (q + 1))] [DecidableEq (r ⊕ s)]
    (i₀ : blockIndex (r ⊕ s) r (q + 1))
    (ψ : (AffineCoefficientField K (MatrixParameters (blockIndex (r ⊕ s) r (q + 1))
      (r ⊕ s)))[X] →+* F) (hψ : Function.Injective ψ) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' ((slEquationMatrix
      (genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) i₀).map ψ))) =
        Fintype.card r * Fintype.card s + 1 := by
  rw [slEquationMatrix_specialized_finrank]
  exact (universal_radical_dimensions q (ψ.comp (affineParameterMap K _))
    (hψ.comp (affineParameterMap_injective K _))).2

theorem generic_pencil_sl_matrix_nullity_tall {K : Type*} {n s : Type} [Field K]
    [Fintype n] [Fintype s] [DecidableEq n] [DecidableEq (n ⊕ s)] [Nonempty n]
    (i₀ : n) :
    Module.finrank (GenericPencilField K n (n ⊕ s))
      (LinearMap.ker (Matrix.toLin' ((slEquationMatrix (genericAffineSquare K n (n ⊕ s))
        (genericAffineRows K n (n ⊕ s)) i₀).map (algebraMap _ (GenericPencilField K n (n ⊕ s)))))) =
          Fintype.card n * Fintype.card s + 1 := by
  rw [slEquationMatrix_specialized_finrank]
  exact (generic_pencil_radical_dimensions_tall (K := K) (n := n) (s := s)).2

end FD56
