/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTerminalObservability

/-! Independent leading rows of the generic observability stack at every wide depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K F n m : Type*} [Field K] [Field F]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
theorem exists_wide_observability_witness (q : ℕ) (hsize : q*Fintype.card m ≤ Fintype.card n) :
    ∃ (M : Matrix n n K) (P : Matrix m n K),
      Function.Surjective (observabilityMatrix M P q).mulVec := by
  classical
  let a := Fin (Fintype.card m)
  let r := Fin (Fintype.card n-q*Fintype.card m)
  let M₀ := (glWitness (0 : Matrix r r K) (0 : Matrix a r K) q).1
  let P₀ := (glWitness (0 : Matrix r r K) (0 : Matrix a r K) q).2
  have hprofile : Module.finrank K (unobservableSpace M₀ P₀ q) = Fintype.card r := by
    simpa [M₀, P₀, unobservableSpace] using
      glWitness_unobservable_finrank (0 : Matrix r r K) (0 : Matrix a r K) q 0
  have hs : Function.Surjective (observabilityMatrix M₀ P₀ q).mulVec := by
    apply observabilityMatrix_surjective
    apply observabilityMap_surjective_of_finrank
    rw [hprofile, blockIndex_card]
    omega
  let ec : n ≃ blockIndex a r q := Fintype.equivOfCardEq (by
    rw [blockIndex_card]
    simp only [a,r,Fintype.card_fin]
    omega)
  let er : m ≃ a := Fintype.equivFin m
  let eRows := Equiv.prodCongr (Equiv.refl (Fin q)) er
  have hpow (k : ℕ) : (M₀.submatrix ec ec)^k = (M₀^k).submatrix ec ec := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, ih, Matrix.submatrix_mul_equiv]
  have he : observabilityMatrix (M₀.submatrix ec ec) (P₀.submatrix er ec) q =
      (observabilityMatrix M₀ P₀ q).submatrix eRows ec := by
    funext i x
    change ((P₀.submatrix er ec)*(M₀.submatrix ec ec)^i.1.val) i.2 x = _
    rw [hpow, Matrix.submatrix_mul_equiv]
    rfl
  refine ⟨M₀.submatrix ec ec, P₀.submatrix er ec, ?_⟩
  rw [he]
  intro w
  obtain ⟨v,hv⟩ := hs (w ∘ eRows.symm)
  refine ⟨v ∘ ec, ?_⟩
  rw [Matrix.submatrix_mulVec_equiv]
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
    hv, Equiv.symm_comp_self, Function.comp_id] using
      (congrArg (fun f => f ∘ eRows) hv)

theorem universal_wide_observability_surjective
    (q : ℕ) (hsize : q*Fintype.card m ≤ Fintype.card n)
    (φ : MvPolynomial (MatrixParameters n m) K →+* F) (hφ : Function.Injective φ) :
    Function.Surjective (observabilityMatrix ((universalSquare K n m).map φ)
      ((universalRows K n m).map φ) q).mulVec := by
  obtain ⟨M,P,hs⟩ := exists_wide_observability_witness (K := K) q hsize
  have he := universal_pair_specialization M P
  have hw : Function.Surjective
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) q).map
        (matrixSpecialization M P)).mulVec := by
    rw [observabilityMatrix_map, he.1, he.2]
    exact hs
  have hh := matrix_surjective_of_specialization MvPolynomial.C (matrixSpecialization M P)
    (fun c => by simp [matrixSpecialization]) φ hφ _ hw
  rwa [observabilityMatrix_map] at hh

theorem generic_observability_leading_pair_surjective
    (q : ℕ) (hsize : q*Fintype.card m ≤ Fintype.card n) :
    Function.Surjective (observabilityMatrix (matrixCoeff (genericAffineSquare K n m) 1)
      (matrixCoeff (genericAffineRows K n m) 1) q).mulVec := by
  rw [(genericAffine_leading_pair K n m).1, (genericAffine_leading_pair K n m).2]
  exact universal_wide_observability_surjective q hsize (affineLeadingParameterMap K _)
    (affineLeadingParameterMap_injective K _)

theorem generic_observability_row_leading_injective
    (q : ℕ) (hsize : q*Fintype.card m ≤ Fintype.card n) :
    Function.Injective (Matrix.mulVec (fun x (ij : Fin q × m) =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q ij x).coeff
        (ij.1.val+1))) := by
  have he : (fun x (ij : Fin q × m) =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q ij x).coeff
        (ij.1.val+1)) =
      (observabilityMatrix (matrixCoeff (genericAffineSquare K n m) 1)
        (matrixCoeff (genericAffineRows K n m) 1) q).transpose := by
    funext x ij
    exact (observability_polynomial_degree_top _ _ q (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) ij x).2
  rw [he]
  exact matrix_transpose_injective_of_surjective _
    (generic_observability_leading_pair_surjective q hsize)

theorem generic_terminal_leading_pair_injective
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m) :
    Function.Injective (observabilityMatrix (matrixCoeff (genericAffineSquare K n m) 1)
      (matrixCoeff (genericAffineRows K n m) 1) (q+1)).mulVec := by
  rw [(genericAffine_leading_pair K n m).1, (genericAffine_leading_pair K n m).2]
  exact universal_terminal_observability_injective q hmn hnm (affineLeadingParameterMap K _)
    (affineLeadingParameterMap_injective K _)

theorem generic_tall_observability_leading_pair_injective
    (q : ℕ) (hsize : Fintype.card n ≤ q*Fintype.card m) :
    Function.Injective (observabilityMatrix (matrixCoeff (genericAffineSquare K n m) 1)
      (matrixCoeff (genericAffineRows K n m) 1) q).mulVec := by
  induction q with
  | zero =>
    have hn : Fintype.card n = 0 := by omega
    letI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    intro v w _
    funext i
    exact isEmptyElim i
  | succ q ih =>
    by_cases hlow : q*Fintype.card m ≤ Fintype.card n
    · exact generic_terminal_leading_pair_injective q hlow hsize
    · have hi := ih (by omega)
      intro v w h
      apply hi
      funext i
      exact congrFun h (i.1.castSucc,i.2)

theorem generic_tall_observability_leading_injective
    (q : ℕ) (hsize : Fintype.card n ≤ q*Fintype.card m) :
    Function.Injective (Matrix.mulVec (fun (ij : Fin q × m) x =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q ij x).coeff
        (ij.1.val+1))) := by
  have he : (fun (ij : Fin q × m) x =>
      (observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) q ij x).coeff
        (ij.1.val+1)) =
      observabilityMatrix (matrixCoeff (genericAffineSquare K n m) 1)
        (matrixCoeff (genericAffineRows K n m) 1) q := by
    funext ij x
    exact (observability_polynomial_degree_top _ _ q (genericAffineSquare_degree K n m)
      (genericAffineRows_degree K n m) ij x).2
  rw [he]
  exact generic_tall_observability_leading_pair_injective q hsize

end FD56
