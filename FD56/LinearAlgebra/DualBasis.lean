/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelBasis
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Complementary blocks of an inverse matrix pair give full kernel bases.
The construction works over a commutative ring, hence for polynomial matrices. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R a r s : Type*} [CommRing R] [Fintype a] [Fintype r] [Fintype s]
  [DecidableEq a] [DecidableEq r] [DecidableEq s]

omit [DecidableEq a] [Fintype r] [Fintype s] in
theorem inversePair_rightRows_mul_leftColumns (U : Matrix a (r ⊕ s) R)
    (V : Matrix (r ⊕ s) a R)
    (hVU : V * U = 1) :
    V.submatrix Sum.inr id * U.submatrix id Sum.inl = 0 := by
  rw [← Matrix.submatrix_mul V U Sum.inr id Sum.inl Function.bijective_id, hVU]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

omit [Fintype a] [DecidableEq a] [DecidableEq r] [DecidableEq s] in
theorem inversePair_leftColumns_mulVec (U : Matrix a (r ⊕ s) R) (c : r → R) :
    U.submatrix id Sum.inl *ᵥ c = U *ᵥ Sum.elim c (0 : s → R) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

def inversePairKernelEquiv (U : Matrix a (r ⊕ s) R) (V : Matrix (r ⊕ s) a R)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    (r → R) ≃ₗ[R] LinearMap.ker (Matrix.toLin' (V.submatrix Sum.inr id)) where
  toFun c := ⟨U *ᵥ Sum.elim c (0 : s → R), by
    have hh : V *ᵥ (U *ᵥ Sum.elim c (0 : s → R)) = Sum.elim c (0 : s → R) := by
      rw [Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]
    funext i
    exact congrFun hh (Sum.inr i)⟩
  invFun y := fun i => (V *ᵥ y.val) (Sum.inl i)
  left_inv c := by
    have hh : V *ᵥ (U *ᵥ Sum.elim c (0 : s → R)) = Sum.elim c (0 : s → R) := by
      rw [Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]
    funext i
    exact congrFun hh (Sum.inl i)
  right_inv y := by
    apply Subtype.ext
    have hz (i : s) : (V *ᵥ y.val) (Sum.inr i) = 0 := congrFun y.property i
    have he : Sum.elim (fun i => (V *ᵥ y.val) (Sum.inl i)) (0 : s → R) = V *ᵥ y.val := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (hz i).symm
    change U *ᵥ Sum.elim _ _ = y.val
    rw [he, Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
  map_add' c c' := by
    apply Subtype.ext
    have he : Sum.elim (c + c') (0 : s → R) =
        Sum.elim c (0 : s → R) + Sum.elim c' (0 : s → R) := by
      funext i
      cases i <;> simp
    change U *ᵥ Sum.elim (c + c') (0 : s → R) = _
    rw [he, Matrix.mulVec_add]
    rfl
  map_smul' a c := by
    apply Subtype.ext
    have he : Sum.elim (a • c) (0 : s → R) = a • Sum.elim c (0 : s → R) := by
      funext i
      cases i <;> simp
    change U *ᵥ Sum.elim (a • c) (0 : s → R) = _
    rw [he, Matrix.mulVec_smul]
    rfl

def inversePairKernelBasis (U : Matrix a (r ⊕ s) R) (V : Matrix (r ⊕ s) a R)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    Basis r R (LinearMap.ker (Matrix.toLin' (V.submatrix Sum.inr id))) :=
  (Pi.basisFun R r).map (inversePairKernelEquiv U V hUV hVU)

theorem inversePairKernelBasis_apply (U : Matrix a (r ⊕ s) R) (V : Matrix (r ⊕ s) a R)
    (hUV : U * V = 1) (hVU : V * U = 1) (j : r) (i : a) :
    (inversePairKernelBasis U V hUV hVU j).val i = U i (Sum.inl j) := by
  change (U *ᵥ Sum.elim ((Pi.basisFun R r) j) (0 : s → R)) i = _
  rw [← inversePair_leftColumns_mulVec]
  simp [Pi.basisFun_apply, Matrix.mulVec_single]

theorem polynomialKernelBasisMatrix_inversePair {K : Type*} [Field K]
    (U : Matrix a (r ⊕ s) K[X]) (V : Matrix (r ⊕ s) a K[X])
    (hUV : U * V = 1) (hVU : V * U = 1) :
    polynomialKernelBasisMatrix (V.submatrix Sum.inr id)
      (inversePairKernelBasis U V hUV hVU) = U.submatrix id Sum.inl := by
  funext i j
  exact inversePairKernelBasis_apply U V hUV hVU j i

def inversePairDualKernelBasis (U : Matrix a (r ⊕ s) R) (V : Matrix (r ⊕ s) a R)
    (hUV : U * V = 1) (hVU : V * U = 1) :
    Basis s R (LinearMap.ker (Matrix.toLin' (U.submatrix id Sum.inl).transpose)) :=
  inversePairKernelBasis
    (V.transpose.submatrix id (Equiv.sumComm s r))
    (U.transpose.submatrix (Equiv.sumComm s r) id)
    (by
      rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, hUV]
      simp)
    (by
      rw [← Matrix.submatrix_mul U.transpose V.transpose (Equiv.sumComm s r) id
        (Equiv.sumComm s r) Function.bijective_id, ← Matrix.transpose_mul, hVU]
      rw [Matrix.transpose_one]
      exact Matrix.submatrix_one_equiv (Equiv.sumComm s r))

theorem inversePairDualKernelBasis_apply (U : Matrix a (r ⊕ s) R)
    (V : Matrix (r ⊕ s) a R) (hUV : U * V = 1) (hVU : V * U = 1) (j : s) (i : a) :
    (inversePairDualKernelBasis U V hUV hVU j).val i = V (Sum.inr j) i := by
  exact inversePairKernelBasis_apply _ _ _ _ j i

theorem polynomialKernelBasisMatrix_inversePairDual {K : Type*} [Field K]
    (U : Matrix a (r ⊕ s) K[X]) (V : Matrix (r ⊕ s) a K[X])
    (hUV : U * V = 1) (hVU : V * U = 1) :
    polynomialKernelBasisMatrix (U.submatrix id Sum.inl).transpose
      (inversePairDualKernelBasis U V hUV hVU) = (V.submatrix Sum.inr id).transpose := by
  funext i j
  exact inversePairDualKernelBasis_apply U V hUV hVU j i

theorem matrix_surjective_of_transpose_injective {K b : Type*} [Field K]
    [Fintype b] [DecidableEq b] (A : Matrix a b K)
    (hA : Function.Injective A.transpose.mulVec) : Function.Surjective A.mulVec := by
  obtain ⟨g, hg⟩ := (Matrix.toLin' A.transpose).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hA)
  let L := LinearMap.toMatrix' g
  have hL : L * A.transpose = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_id] using congrArg LinearMap.toMatrix' hg
  have ht : A * L.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]
      using congrArg Matrix.transpose hL
  intro v
  refine ⟨L.transpose *ᵥ v, ?_⟩
  rw [Matrix.mulVec_mulVec, ht, Matrix.one_mulVec]

end FD56
