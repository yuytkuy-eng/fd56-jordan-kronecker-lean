/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityMatrix
import FD56.Stabilizer.RegularWitness
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Localization.FractionRing

/-! Generic observability and radical dimensions, proved by specialization
to an explicit full-rank pair. -/

noncomputable section
namespace FD56
open Matrix

theorem observability_profile_of_specialization {R K F n m : Type*}
    [CommRing R] [Field K] [Field F] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m]
    (ι : K →+* R) (ψ : R →+* K) (hι : ∀ c, ψ (ι c) = c)
    (φ : R →+* F) (hφ : Function.Injective φ)
    (M : Matrix n n R) (P : Matrix m n R) (q ρ : ℕ)
    (hsize : Fintype.card n = (q + 1) * Fintype.card m + ρ)
    (hfirst : Module.finrank K (unobservableSpace (M.map ψ) (P.map ψ) (q + 1)) = ρ)
    (hnext : Module.finrank K (unobservableSpace (M.map ψ) (P.map ψ) (q + 2)) = 0) :
    Module.finrank F (unobservableSpace (M.map φ) (P.map φ) (q + 1)) = ρ ∧
    Module.finrank F (unobservableSpace (M.map φ) (P.map φ) (q + 2)) = 0 := by
  have hsurj : Function.Surjective ((observabilityMatrix M P (q + 1)).map ψ).mulVec := by
    rw [observabilityMatrix_map]
    apply observabilityMatrix_surjective
    apply observabilityMap_surjective_of_finrank
    rw [hfirst]
    omega
  have hinj : Function.Injective ((observabilityMatrix M P (q + 2)).map ψ).mulVec := by
    rw [observabilityMatrix_map]
    change Function.Injective (Matrix.toLin' (observabilityMatrix (M.map ψ) (P.map ψ) (q + 2)))
    apply LinearMap.ker_eq_bot.mp
    rw [observabilityMatrix_ker]
    exact Submodule.finrank_eq_zero.mp hnext
  have hs := matrix_surjective_of_specialization ι ψ hι φ hφ _ hsurj
  have hi := matrix_injective_of_specialization ι ψ hι φ hφ _ hinj
  rw [observabilityMatrix_map] at hs hi
  constructor
  · have hd := (Matrix.toLin' (observabilityMatrix (M.map φ) (P.map φ) (q + 1))).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hs, observabilityMatrix_ker] at hd
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_prod,
      Fintype.card_fin] at hd
    omega
  · have hk : LinearMap.ker (Matrix.toLin' (observabilityMatrix (M.map φ) (P.map φ) (q + 2))) = ⊥ :=
      LinearMap.ker_eq_bot.mpr hi
    rw [observabilityMatrix_ker] at hk
    rw [hk, finrank_bot]

abbrev MatrixParameters (n m : Type*) := (n × n) ⊕ (m × n)

def universalSquare (K n m : Type*) [CommRing K] :
    Matrix n n (MvPolynomial (MatrixParameters n m) K) :=
  fun i j => MvPolynomial.X (Sum.inl (i, j))

def universalRows (K n m : Type*) [CommRing K] :
    Matrix m n (MvPolynomial (MatrixParameters n m) K) :=
  fun i j => MvPolynomial.X (Sum.inr (i, j))

def matrixSpecialization {K n m : Type*} [CommRing K]
    (M : Matrix n n K) (P : Matrix m n K) : MvPolynomial (MatrixParameters n m) K →+* K :=
  MvPolynomial.eval₂Hom (RingHom.id K)
    (Sum.elim (fun ij => M ij.1 ij.2) (fun ij => P ij.1 ij.2))

theorem universal_pair_specialization {K n m : Type*} [CommRing K]
    (M : Matrix n n K) (P : Matrix m n K) :
    (universalSquare K n m).map (matrixSpecialization M P) = M ∧
      (universalRows K n m).map (matrixSpecialization M P) = P := by
  constructor <;> ext i j <;>
    simp [universalSquare, universalRows, matrixSpecialization]

theorem universal_observability_profile {K F n m : Type*} [Field K] [Field F]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (φ : MvPolynomial (MatrixParameters n m) K →+* F) (hφ : Function.Injective φ)
    (M₀ : Matrix n n K) (P₀ : Matrix m n K) (q ρ : ℕ)
    (hsize : Fintype.card n = (q + 1) * Fintype.card m + ρ)
    (hfirst : Module.finrank K (unobservableSpace M₀ P₀ (q + 1)) = ρ)
    (hnext : Module.finrank K (unobservableSpace M₀ P₀ (q + 2)) = 0) :
    Module.finrank F (unobservableSpace ((universalSquare K n m).map φ)
      ((universalRows K n m).map φ) (q + 1)) = ρ ∧
    Module.finrank F (unobservableSpace ((universalSquare K n m).map φ)
      ((universalRows K n m).map φ) (q + 2)) = 0 := by
  have he := universal_pair_specialization M₀ P₀
  apply observability_profile_of_specialization MvPolynomial.C (matrixSpecialization M₀ P₀)
    (fun c => by simp [matrixSpecialization]) φ hφ _ _ q ρ hsize
  · rw [he.1, he.2]
    exact hfirst
  · rw [he.1, he.2]
    exact hnext

theorem universal_radical_dimensions {K F : Type*} {r s : Type}
    [Field K] [Field F] [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ)
    (φ : MvPolynomial (MatrixParameters (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) K →+* F)
    (hφ : Function.Injective φ) :
    Module.finrank F (glStabilizerSpace
      ((universalSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)).map φ)
      ((universalRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)).map φ)) =
        Fintype.card r * Fintype.card s ∧
    Module.finrank F (fieldSLRadical
      ((universalSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)).map φ)
      ((universalRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)).map φ)) =
        Fintype.card r * Fintype.card s + 1 := by
  classical
  letI : Nonempty (blockIndex (r ⊕ s) r (q + 1)) :=
    inferInstanceAs (Nonempty ((r ⊕ s) ⊕ blockIndex (r ⊕ s) r q))
  obtain ⟨M₀, P₀, hf, hn⟩ := exists_regular_observability_pair (K := K) (r := r) (s := s) q
  have hsize := blockIndex_card (m := r ⊕ s) (r := r) (q + 1)
  obtain ⟨hfirst, hnext⟩ := universal_observability_profile φ hφ M₀ P₀ q
    (Fintype.card r) hsize hf hn
  constructor
  · have h := gl_finrank_of_observability q (Fintype.card r) _ _ hsize hfirst hnext
    simpa only [Fintype.card_sum, Nat.add_sub_cancel_left] using h
  · have h := sl_finrank_of_observability q (Fintype.card r) _ _ hsize hfirst hnext
    simpa only [Fintype.card_sum, Nat.add_sub_cancel_left] using h

theorem universal_radical_dimensions_tall {K F : Type*} {n s : Type}
    [Field K] [Field F] [Fintype n] [Fintype s] [DecidableEq n] [Nonempty n]
    (φ : MvPolynomial (MatrixParameters n (n ⊕ s)) K →+* F)
    (hφ : Function.Injective φ) :
    Module.finrank F (glStabilizerSpace ((universalSquare K n (n ⊕ s)).map φ)
      ((universalRows K n (n ⊕ s)).map φ)) = Fintype.card n * Fintype.card s ∧
    Module.finrank F (fieldSLRadical ((universalSquare K n (n ⊕ s)).map φ)
      ((universalRows K n (n ⊕ s)).map φ)) = Fintype.card n * Fintype.card s + 1 := by
  classical
  let P₀ : Matrix (n ⊕ s) n K := Matrix.fromRows 1 0
  let L₀ : Matrix n (n ⊕ s) K := Matrix.fromCols 1 0
  let ψ := matrixSpecialization (0 : Matrix n n K) P₀
  have hL : L₀ * P₀ = 1 := by simp [P₀, L₀, Matrix.fromCols_mul_fromRows]
  have hP₀ : Function.Injective P₀.mulVec := by
    intro v w h
    have hh := congrArg (fun z => L₀ *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using hh
  have he := (universal_pair_specialization (0 : Matrix n n K) P₀).2
  have hp : Function.Injective (((universalRows K n (n ⊕ s)).map φ).mulVec) := by
    apply matrix_injective_of_specialization MvPolynomial.C ψ
      (fun c => by simp [ψ, matrixSpecialization]) φ hφ
    rw [he]
    exact hP₀
  have hg := gl_base_finrank_of_injective ((universalSquare K n (n ⊕ s)).map φ)
    ((universalRows K n (n ⊕ s)).map φ) hp
  have hd : Module.finrank F (glStabilizerSpace ((universalSquare K n (n ⊕ s)).map φ)
      ((universalRows K n (n ⊕ s)).map φ)) = Fintype.card n * Fintype.card s := by
    simpa only [Fintype.card_sum, Nat.add_sub_cancel_left] using hg
  refine ⟨hd, ?_⟩
  have ho : unobservableSpace ((universalSquare K n (n ⊕ s)).map φ)
      ((universalRows K n (n ⊕ s)).map φ) 1 = ⊥ := by
    simp only [unobservableSpace, Submodule.comap_top, inf_top_eq]
    exact LinearMap.ker_eq_bot.mpr hp
  have hz : Module.finrank F (unobservableSpace ((universalSquare K n (n ⊕ s)).map φ)
      ((universalRows K n (n ⊕ s)).map φ) 1) = 0 := by rw [ho, finrank_bot]
  rw [observable_sl_radical_finrank _ _ 1 hz, hd]

abbrev GenericMatrixField (K n m : Type*) [CommRing K] :=
  FractionRing (MvPolynomial (MatrixParameters n m) K)

def genericSquare (K n m : Type*) [Field K] : Matrix n n (GenericMatrixField K n m) :=
  (universalSquare K n m).map (algebraMap (MvPolynomial (MatrixParameters n m) K) _)

def genericRows (K n m : Type*) [Field K] : Matrix m n (GenericMatrixField K n m) :=
  (universalRows K n m).map (algebraMap (MvPolynomial (MatrixParameters n m) K) _)

theorem generic_radical_dimensions {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] [Nonempty (r ⊕ s)] (q : ℕ) :
    Module.finrank (GenericMatrixField K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (glStabilizerSpace (genericSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))) =
        Fintype.card r * Fintype.card s ∧
    Module.finrank (GenericMatrixField K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
      (fieldSLRadical (genericSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))
        (genericRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s))) =
        Fintype.card r * Fintype.card s + 1 :=
  universal_radical_dimensions q _ (IsFractionRing.injective _ _)

theorem generic_radical_dimensions_tall {K : Type*} {n s : Type} [Field K]
    [Fintype n] [Fintype s] [DecidableEq n] [Nonempty n] :
    Module.finrank (GenericMatrixField K n (n ⊕ s))
      (glStabilizerSpace (genericSquare K n (n ⊕ s)) (genericRows K n (n ⊕ s))) =
        Fintype.card n * Fintype.card s ∧
    Module.finrank (GenericMatrixField K n (n ⊕ s))
      (fieldSLRadical (genericSquare K n (n ⊕ s)) (genericRows K n (n ⊕ s))) =
        Fintype.card n * Fintype.card s + 1 :=
  universal_radical_dimensions_tall _ (IsFractionRing.injective _ _)

end FD56
