/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericActualDepthTwoStack
import FD56.Stabilizer.GenericMiddleRank
import FD56.Stabilizer.RegularWitness

/-! The third observability block is injective on the generic depth-two kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K F n m : Type*} [Field K] [Field F]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
theorem exists_depth_two_observability_witness
    (hmn : 2*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ 3*Fintype.card m) :
    ∃ (M : Matrix n n K) (P : Matrix m n K),
      Function.Injective (observabilityMatrix M P 3).mulVec := by
  classical
  let r := Fin (Fintype.card n-2*Fintype.card m)
  let a := Fin (Fintype.card m)
  let e : r ↪ a := (Function.Embedding.nonempty_of_card_le
    (show Fintype.card r ≤ Fintype.card a by simp [r,a]; omega)).some
  let B : Matrix a r K := fun i j => if e j=i then 1 else 0
  have hB : Function.Injective B.mulVec := by
    intro v w h
    funext j
    have hh := congrFun h (e j)
    have hv (z : r → K) : (B *ᵥ z) (e j) = z j := by
      change (∑ k, (if e k=e j then (1 : K) else 0)*z k) = z j
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have he : e k ≠ e j := fun he => hk (e.injective he)
        simp [he]
      · simp
    exact (hv v).symm.trans (hh.trans (hv w))
  obtain ⟨L,hL⟩ := matrix_left_inverse_of_injective B hB
  let M₀ := (glWitness (0 : Matrix r r K) B 2).1
  let P₀ := (glWitness (0 : Matrix r r K) B 2).2
  have hprofile := (glWitness_observability_profile (0 : Matrix r r K) B L hL 2).2
  have hi : Function.Injective (observabilityMatrix M₀ P₀ 3).mulVec := by
    change Function.Injective (Matrix.toLin' (observabilityMatrix M₀ P₀ 3))
    apply LinearMap.ker_eq_bot.mp
    rw [observabilityMatrix_ker]
    exact Submodule.finrank_eq_zero.mp hprofile
  let ec : n ≃ blockIndex a r 2 := Fintype.equivOfCardEq (by
    rw [blockIndex_card]
    simp only [a,r,Fintype.card_fin]
    omega)
  let er : m ≃ a := Fintype.equivFin m
  have hpow (k : ℕ) : (M₀.submatrix ec ec)^k = (M₀^k).submatrix ec ec := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,pow_succ,ih,Matrix.submatrix_mul_equiv]
  have he : observabilityMatrix (M₀.submatrix ec ec) (P₀.submatrix er ec) 3 =
      (observabilityMatrix M₀ P₀ 3).submatrix (Equiv.prodCongr (Equiv.refl _) er) ec := by
    funext i x
    change ((P₀.submatrix er ec)*(M₀.submatrix ec ec)^i.1.val) i.2 x = _
    rw [hpow,Matrix.submatrix_mul_equiv]
    rfl
  refine ⟨M₀.submatrix ec ec,P₀.submatrix er ec,?_⟩
  rw [he]
  intro v w h
  rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv] at h
  have hh : (observabilityMatrix M₀ P₀ 3) *ᵥ (v ∘ ec.symm) =
      (observabilityMatrix M₀ P₀ 3) *ᵥ (w ∘ ec.symm) := by
    funext i
    simpa only [Function.comp_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
      Equiv.apply_symm_apply,Prod.mk.eta] using congrFun h (i.1,er.symm i.2)
  have hv := hi hh
  funext j
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun hv (ec j)

theorem universal_depth_two_observability_injective
    (hmn : 2*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ 3*Fintype.card m)
    (φ : MvPolynomial (MatrixParameters n m) K →+* F) (hφ : Function.Injective φ) :
    Function.Injective (observabilityMatrix ((universalSquare K n m).map φ)
      ((universalRows K n m).map φ) 3).mulVec := by
  obtain ⟨M,P,hi⟩ := exists_depth_two_observability_witness (K := K) hmn hnm
  have he := universal_pair_specialization M P
  have hw : Function.Injective
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) 3).map
        (matrixSpecialization M P)).mulVec := by
    rw [observabilityMatrix_map,he.1,he.2]
    exact hi
  have hh := matrix_injective_of_specialization MvPolynomial.C (matrixSpecialization M P)
    (fun c => by simp [matrixSpecialization]) φ hφ _ hw
  rwa [observabilityMatrix_map] at hh

theorem generic_depth_two_observability_zero_injective
    (hmn : 2*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ 3*Fintype.card m) :
    Function.Injective ((observabilityMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) 3).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom (0 : AffineCoefficientField K (MatrixParameters n m))).comp
    (affineParameterMap K (MatrixParameters n m))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
      (AffineCoefficientField K (MatrixParameters n m))).comp
      (MvPolynomial.rename_injective (R := K)
        (Sum.inl : MatrixParameters n m → MatrixParameters n m ⊕ MatrixParameters n m)
        Sum.inl_injective)
  rw [observabilityMatrix_map]
  change Function.Injective (observabilityMatrix
    (((universalSquare K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0))
    (((universalRows K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0)) 3).mulVec
  rw [Matrix.map_map,Matrix.map_map]
  exact universal_depth_two_observability_injective hmn hnm φ hφ

theorem generic_depth_two_observability_injective
    (hmn : 2*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ 3*Fintype.card m) :
    Function.Injective (observabilityMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) 3).mulVec :=
  polynomial_matrix_injective_of_zero _ (generic_depth_two_observability_zero_injective hmn hnm)

omit [Fintype m] [DecidableEq m] in
theorem depthTwo_kernel_transfer_injective {r : Type*} [Fintype r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (hO : Function.Injective (observabilityMatrix M P 3).mulVec) :
    Function.Injective (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).mulVec := by
  let V := polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B
  have hPV : P*V=0 := by
    funext i j
    exact congrFun (congrFun (polynomialKernelBasisMatrix_mul _ B) (Sum.inl i)) j
  have hPMV : P*M*V=0 := by
    funext i j
    exact congrFun (congrFun (polynomialKernelBasisMatrix_mul _ B) (Sum.inr i)) j
  intro c d h
  apply polynomialKernelBasisMatrix_injective _ B
  apply hO
  funext i
  rcases i with ⟨i,x⟩
  fin_cases i
  · change ((P*1) *ᵥ (V*ᵥ c)) x = ((P*1) *ᵥ (V*ᵥ d)) x
    rw [Matrix.mul_one,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hPV,
      Matrix.zero_mulVec,Matrix.zero_mulVec]
  · change ((P*M^1) *ᵥ (V*ᵥ c)) x = ((P*M^1) *ᵥ (V*ᵥ d)) x
    rw [pow_one,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hPMV,
      Matrix.zero_mulVec,Matrix.zero_mulVec]
  · change ((P*M^2) *ᵥ (V*ᵥ c)) x = ((P*M^2) *ᵥ (V*ᵥ d)) x
    rw [pow_two,← Matrix.mul_assoc,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    exact congrFun h x

theorem generic_depth_two_kernel_transfer_injective {r : Type*} [Fintype r]
    (hmn : 2*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ 3*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (depthTwoStack (genericAffineRows K n m)
        (genericAffineRows K n m*genericAffineSquare K n m))))) :
    Function.Injective (genericAffineRows K n m*genericAffineSquare K n m*genericAffineSquare K n m*
      polynomialKernelBasisMatrix _ B).mulVec :=
  depthTwo_kernel_transfer_injective _ _ B (generic_depth_two_observability_injective hmn hnm)

end FD56
