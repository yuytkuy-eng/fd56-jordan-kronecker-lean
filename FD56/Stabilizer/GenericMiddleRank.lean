/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericRows
import FD56.Hilbert.MiddleGL

/-! Two generic observability blocks have full column rank when n ≤ 2m.
Their restriction to any polynomial basis of ker P remains injective. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem fromRows_map_eq {R S a b c : Type*} (A : Matrix a c R) (B : Matrix b c R)
    (f : R → S) : (Matrix.fromRows A B).map f = Matrix.fromRows (A.map f) (B.map f) := by
  funext i j
  cases i <;> rfl

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [DecidableEq n] in
theorem exists_middle_observability_witness
    (hmn : Fintype.card m ≤ Fintype.card n) (hnm : Fintype.card n ≤ 2 * Fintype.card m) :
    ∃ (M : Matrix n n K) (P : Matrix m n K),
      Function.Injective (Matrix.fromRows P (P * M)).mulVec := by
  classical
  let r := Fin (Fintype.card n - Fintype.card m)
  have hr : Fintype.card r ≤ Fintype.card m := by simp [r]; omega
  let e : r ↪ m := Classical.choice (Function.Embedding.nonempty_of_card_le hr)
  let B : Matrix m r K := fun i j => if i = e j then 1 else 0
  have hB : Function.Injective B.mulVec := by
    intro v w h
    funext j
    have hh := congrFun h (e j)
    have hv (z : r → K) : (B *ᵥ z) (e j) = z j := by
      change (∑ k, (if e j = e k then (1 : K) else 0) * z k) = z j
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have he : e j ≠ e k := fun h => hk (e.injective h).symm
        simp [he]
      · simp
    exact (hv v).symm.trans (hh.trans (hv w))
  let P₀ : Matrix m (m ⊕ r) K := Matrix.fromCols 1 0
  let M₀ : Matrix (m ⊕ r) (m ⊕ r) K := Matrix.fromBlocks 0 B 0 0
  have hA : Function.Injective (Matrix.fromRows P₀ (P₀ * M₀)).mulVec := by
    have he : Matrix.fromRows P₀ (P₀ * M₀) =
        Matrix.fromBlocks (1 : Matrix m m K) (0 : Matrix m r K) (0 : Matrix m m K) B := by
      simp [P₀, M₀, Matrix.fromCols_mul_fromBlocks, Matrix.fromRows_fromCols_eq_fromBlocks]
    rw [he]
    intro v w h
    have hleft : (fun i => v (Sum.inl i)) = (fun i => w (Sum.inl i)) := by
      funext i
      have hh := congrFun h (Sum.inl i)
      simpa [Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type,
        Matrix.one_apply] using hh
    have hright : (fun i => v (Sum.inr i)) = (fun i => w (Sum.inr i)) := by
      apply hB
      funext i
      have hh := congrFun h (Sum.inr i)
      simpa [Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type] using hh
    funext i
    cases i with
    | inl i => exact congrFun hleft i
    | inr i => exact congrFun hright i
  let ec : n ≃ m ⊕ r := Fintype.equivOfCardEq (by simp [r]; omega)
  refine ⟨M₀.submatrix ec ec, P₀.submatrix id ec, ?_⟩
  rw [Matrix.submatrix_mul_equiv]
  have he : Matrix.fromRows (P₀.submatrix id ec) ((P₀ * M₀).submatrix id ec) =
      (Matrix.fromRows P₀ (P₀ * M₀)).submatrix id ec := by
    funext i j
    cases i <;> rfl
  rw [he]
  intro v w h
  rw [Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv] at h
  have hh := hA h
  funext j
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using congrFun hh (ec j)

theorem universal_middle_observability_injective {F : Type*} [Field F]
    (hnm : Fintype.card n ≤ 2 * Fintype.card m)
    (φ : MvPolynomial (MatrixParameters n m) K →+* F) (hφ : Function.Injective φ) :
    Function.Injective (Matrix.fromRows ((universalRows K n m).map φ)
      (((universalRows K n m).map φ) * ((universalSquare K n m).map φ))).mulVec := by
  by_cases hsmall : Fintype.card n ≤ Fintype.card m
  · have hP := universal_rows_injective_of_sizes hsmall φ hφ
    intro v w h
    apply hP
    funext i
    exact congrFun h (Sum.inl i)
  · obtain ⟨M, P, hi⟩ := exists_middle_observability_witness (K := K) (by omega) hnm
    have he := universal_pair_specialization M P
    have hw : Function.Injective
        ((Matrix.fromRows (universalRows K n m)
          (universalRows K n m * universalSquare K n m)).map (matrixSpecialization M P)).mulVec := by
      rw [fromRows_map_eq, Matrix.map_mul, he.1, he.2]
      exact hi
    have hh := matrix_injective_of_specialization MvPolynomial.C (matrixSpecialization M P)
      (fun c => by simp [matrixSpecialization]) φ hφ _ hw
    simpa only [fromRows_map_eq, Matrix.map_mul] using hh

theorem generic_middle_observability_zero_injective
    (hnm : Fintype.card n ≤ 2 * Fintype.card m) :
    Function.Injective ((Matrix.fromRows (genericAffineRows K n m)
      (genericAffineRows K n m * genericAffineSquare K n m)).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom (0 : AffineCoefficientField K (MatrixParameters n m))).comp
    (affineParameterMap K (MatrixParameters n m))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
      (AffineCoefficientField K (MatrixParameters n m))).comp
      (MvPolynomial.rename_injective (R := K)
        (Sum.inl : MatrixParameters n m → MatrixParameters n m ⊕ MatrixParameters n m) Sum.inl_injective)
  rw [fromRows_map_eq, Matrix.map_mul]
  change Function.Injective (Matrix.fromRows
    (((universalRows K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0))
    ((((universalRows K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0)) *
      (((universalSquare K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0)))).mulVec
  rw [Matrix.map_map, Matrix.map_map]
  exact universal_middle_observability_injective hnm φ hφ

theorem generic_middle_observability_injective
    (hnm : Fintype.card n ≤ 2 * Fintype.card m) :
    Function.Injective (Matrix.fromRows (genericAffineRows K n m)
      (genericAffineRows K n m * genericAffineSquare K n m)).mulVec :=
  polynomial_matrix_injective_of_zero _ (generic_middle_observability_zero_injective hnm)

omit [Fintype m] [DecidableEq m] in
theorem middle_kernel_transfer_injective {r : Type*} [Fintype r]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (hO : Function.Injective (Matrix.fromRows P (P * M)).mulVec) :
    Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec := by
  let V := polynomialKernelBasisMatrix P B
  have hPV : P * V = 0 := polynomialKernelBasisMatrix_mul P B
  dsimp only [V] at hPV
  intro c d h
  apply polynomialKernelBasisMatrix_injective P B
  apply hO
  rw [Matrix.fromRows_mulVec, Matrix.fromRows_mulVec]
  funext i
  cases i with
  | inl i => simp only [Sum.elim_inl, Matrix.mulVec_mulVec, hPV, Matrix.zero_mulVec]
  | inr i =>
    simpa only [Sum.elim_inr, Matrix.mulVec_mulVec] using congrFun h i

theorem generic_middle_kernel_transfer_injective {r : Type*} [Fintype r]
    (hnm : Fintype.card n ≤ 2 * Fintype.card m)
    (B : Basis r (Polynomial (AffineCoefficientField K (MatrixParameters n m)))
      (LinearMap.ker (Matrix.toLin' (genericAffineRows K n m)))) :
    Function.Injective (genericAffineRows K n m * genericAffineSquare K n m *
      polynomialKernelBasisMatrix (genericAffineRows K n m) B).mulVec :=
  middle_kernel_transfer_injective _ _ B (generic_middle_observability_injective hnm)

end FD56
