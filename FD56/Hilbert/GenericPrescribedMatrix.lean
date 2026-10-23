/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PrescribedDegrees
import FD56.Hilbert.ColumnSurjectivity
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Independently generic polynomial matrices with prescribed row degrees
have the smallest bounded kernels allowed by their coefficient dimensions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

abbrev PrescribedMatrixParameters {m : Type*} (n : Type*) (e : m → ℕ) :=
  Σ i : m, n × Fin (e i + 1)

abbrev PrescribedMatrixField (K n : Type*) {m : Type*} [Field K] (e : m → ℕ) :=
  FractionRing (MvPolynomial (PrescribedMatrixParameters n e) K)

def universalPrescribedMatrix (K n : Type*) {m : Type*} [Field K] (e : m → ℕ) :
    Matrix m n (MvPolynomial (PrescribedMatrixParameters n e) K)[X] := by
  classical
  exact fun i j => Polynomial.ofFn (e i + 1) (fun k => MvPolynomial.X ⟨i, j, k⟩)

def genericPrescribedMatrix (K n : Type*) {m : Type*} [Field K] (e : m → ℕ) :
    Matrix m n (PrescribedMatrixField K n e)[X] :=
  (universalPrescribedMatrix K n e).map (Polynomial.mapRingHom
    (algebraMap (MvPolynomial (PrescribedMatrixParameters n e) K) (PrescribedMatrixField K n e)))

variable {K L m n : Type*} [Field K] [Field L]

theorem universalPrescribedMatrix_degree (e : m → ℕ) (i : m) (j : n) :
    (universalPrescribedMatrix K n e i j).natDegree ≤ e i := by
  classical
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega) _)

theorem genericPrescribedMatrix_degree (e : m → ℕ) (i : m) (j : n) :
    (genericPrescribedMatrix K n e i j).natDegree ≤ e i :=
  Polynomial.natDegree_map_le.trans (universalPrescribedMatrix_degree e i j)

def prescribedMatrixSpecialization (e : m → ℕ) (σ : K →+* L) (P : Matrix m n L[X]) :
    MvPolynomial (PrescribedMatrixParameters n e) K →+* L :=
  MvPolynomial.eval₂Hom σ (fun p => (P p.1 p.2.1).coeff p.2.2.val)

theorem universalPrescribedMatrix_specialization (e : m → ℕ) (σ : K →+* L)
    (P : Matrix m n L[X]) (hP : ∀ i j, (P i j).natDegree ≤ e i) :
    (universalPrescribedMatrix K n e).map
      (Polynomial.mapRingHom (prescribedMatrixSpecialization e σ P)) = P := by
  classical
  funext i j
  change (Polynomial.ofFn (e i + 1) _).map _ = P i j
  calc
    _ = Polynomial.ofFn (e i + 1) (fun k => (P i j).coeff k.val) := by
      simp only [Polynomial.ofFn_eq_sum_monomial, Polynomial.map_sum,
        Polynomial.map_monomial, prescribedMatrixSpecialization, MvPolynomial.eval₂Hom_X']
    _ = P i j := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := hP i j; omega)

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem generic_prescribed_kernel_le_witness (e : m → ℕ) (σ : K →+* L)
    (P : Matrix m n L[X]) (hP : ∀ i j, (P i j).natDegree ≤ e i) (d : ℕ) :
    Module.finrank (PrescribedMatrixField K n e)
      (polynomialKernelAtDegree (genericPrescribedMatrix K n e) d) ≤
      Module.finrank L (polynomialKernelAtDegree P d) := by
  let ψ := prescribedMatrixSpecialization e σ P
  let φ := algebraMap (MvPolynomial (PrescribedMatrixParameters n e) K)
    (PrescribedMatrixField K n e)
  let C := weightedCoefficientMatrix (universalPrescribedMatrix K n e)
    (fun _ => d) (fun i => d + e i)
  have he : C.map ψ = weightedCoefficientMatrix P (fun _ => d) (fun i => d + e i) := by
    dsimp only [C, ψ]
    rw [← weightedCoefficientMatrix_map, universalPrescribedMatrix_specialization e σ P hP]
  have hg : C.map φ = weightedCoefficientMatrix (genericPrescribedMatrix K n e)
      (fun _ => d) (fun i => d + e i) := by
    exact (weightedCoefficientMatrix_map _ _ _ _).symm
  have hs := matrix_kernel_finrank_le_of_field_specialization ψ φ
    (IsFractionRing.injective _ _) C
  rw [he, hg, weighted_coefficient_kernel_finrank _ _ _ (by
    intro i j
    have := genericPrescribedMatrix_degree (K := K) (n := n) e i j
    omega), weighted_coefficient_kernel_finrank _ _ _ (by
      intro i j
      have := hP i j
      omega)] at hs
  exact hs

omit [DecidableEq m] in
theorem prescribed_matrix_kernel_lower (P : Matrix m n K[X]) (e : m → ℕ)
    (hP : ∀ i j, (P i j).natDegree ≤ e i) (hmn : Fintype.card m ≤ Fintype.card n)
    (d : ℕ) :
    (Fintype.card n - Fintype.card m) * (d + 1) - ∑ i, e i ≤
      Module.finrank K (polynomialKernelAtDegree P d) := by
  let C := weightedCoefficientMatrix P (fun _ => d) (fun i => d + e i)
  have he := (Matrix.toLin' C).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (Matrix.toLin' C))
  have hk : Module.finrank K (LinearMap.ker (Matrix.toLin' C)) =
      Module.finrank K (polynomialKernelAtDegree P d) :=
    weighted_coefficient_kernel_finrank _ _ _ (by
      intro i j
      have := hP i j
      omega)
  rw [hk] at he
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at he hr
  have hout : (∑ i : m, (d + e i + 1)) = Fintype.card m * (d + 1) + ∑ i, e i := by
    simp_rw [show ∀ i, d + e i + 1 = (d + 1) + e i by intro i; omega]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  rw [hout] at hr
  have hm : Fintype.card n = Fintype.card m + (Fintype.card n - Fintype.card m) := by omega
  rw [hm, Nat.add_mul] at he
  omega

theorem generic_prescribed_kernel_hilbert (e : m → ℕ)
    (hmn : Fintype.card m < Fintype.card n) (d : ℕ) :
    Module.finrank (PrescribedMatrixField K n e)
      (polynomialKernelAtDegree (genericPrescribedMatrix K n e) d) =
      (Fintype.card n - Fintype.card m) * (d + 1) - ∑ i, e i := by
  apply le_antisymm
  · obtain ⟨F, hF, hH⟩ := exists_prescribed_column_matrix_balanced_kernel (K := K) e hmn
    have hh := generic_prescribed_kernel_le_witness e (RingHom.id K) F.transpose
      (fun i j => hF j i) d
    exact hh.trans_eq (hH d)
  · exact prescribed_matrix_kernel_lower _ e
      (genericPrescribedMatrix_degree (K := K) (n := n) e) hmn.le d

theorem generic_prescribed_coefficient_injective (e : m → ℕ)
    (hmn : Fintype.card m < Fintype.card n) (d : ℕ)
    (hd : (Fintype.card n - Fintype.card m) * (d + 1) ≤ ∑ i, e i) :
    Function.Injective (weightedCoefficientMatrix (genericPrescribedMatrix K n e)
      (fun _ => d) (fun i => d + e i)).mulVec := by
  apply weighted_coefficient_injective_of_kernel_zero
  · intro i j
    have := genericPrescribedMatrix_degree (K := K) (n := n) e i j
    omega
  · rw [weighted_uniform_kernel, generic_prescribed_kernel_hilbert e hmn d,
      Nat.sub_eq_zero_of_le hd]

theorem generic_prescribed_coefficient_surjective (e : m → ℕ)
    (hmn : Fintype.card m < Fintype.card n) (d : ℕ)
    (hd : ∑ i, e i ≤ (Fintype.card n - Fintype.card m) * (d + 1)) :
    Function.Surjective (weightedCoefficientMatrix (genericPrescribedMatrix K n e)
      (fun _ => d) (fun i => d + e i)).mulVec :=
  column_coefficient_surjective_of_kernel_hilbert
    (genericPrescribedMatrix K n e).transpose e d
    (fun j i => genericPrescribedMatrix_degree e i j) hmn.le hd
    (generic_prescribed_kernel_hilbert e hmn d)

omit [Fintype m] in
theorem generic_prescribed_submatrix_kernel_hilbert
    {l : Type*} [Fintype l] [DecidableEq l] (e : m → ℕ) (u : l ↪ m)
    (hln : Fintype.card l < Fintype.card n) (d : ℕ) :
    Module.finrank (PrescribedMatrixField K n e)
      (polynomialKernelAtDegree ((genericPrescribedMatrix K n e).submatrix u id) d) =
      (Fintype.card n - Fintype.card l) * (d + 1) - ∑ i, e (u i) := by
  classical
  apply le_antisymm
  · obtain ⟨W, hW, hH⟩ := exists_prescribed_column_matrix_balanced_kernel (K := K)
      (fun i => e (u i)) hln
    let P : Matrix m n K[X] := Function.extend u W.transpose 0
    have hPu : P.submatrix u id = W.transpose := by
      funext i j
      exact congrFun (u.injective.extend_apply W.transpose 0 i) j
    have hP : ∀ i j, (P i j).natDegree ≤ e i := by
      intro i j
      by_cases hi : ∃ x, u x = i
      · obtain ⟨x, rfl⟩ := hi
        change (P.submatrix u id x j).natDegree ≤ _
        rw [hPu]
        exact hW j x
      · have hp : P i = 0 := Function.extend_apply' (f := u) W.transpose
          (0 : Matrix m n K[X]) i hi
        rw [hp]
        simp
    let ψ := prescribedMatrixSpecialization e (RingHom.id K) P
    let φ := algebraMap (MvPolynomial (PrescribedMatrixParameters n e) K)
      (PrescribedMatrixField K n e)
    let C := weightedCoefficientMatrix ((universalPrescribedMatrix K n e).submatrix u id)
      (fun _ => d) (fun i => d + e (u i))
    have he : C.map ψ = weightedCoefficientMatrix W.transpose
        (fun _ => d) (fun i => d + e (u i)) := by
      dsimp only [C, ψ]
      rw [← weightedCoefficientMatrix_map, ← Matrix.submatrix_map,
        universalPrescribedMatrix_specialization e (RingHom.id K) P hP, hPu]
    have hg : C.map φ = weightedCoefficientMatrix
        ((genericPrescribedMatrix K n e).submatrix u id)
        (fun _ => d) (fun i => d + e (u i)) := by
      rw [← weightedCoefficientMatrix_map]
      rfl
    have hh := matrix_kernel_finrank_le_of_field_specialization ψ φ
      (IsFractionRing.injective _ _) C
    rw [he, hg, weighted_coefficient_kernel_finrank _ _ _ (by
      intro i j
      have := genericPrescribedMatrix_degree (K := K) (n := n) e (u i) j
      exact Nat.add_le_add_right this d |>.trans (by omega)),
      weighted_coefficient_kernel_finrank _ _ _ (by
        intro i j
        have := hW j i
        exact Nat.add_le_add_right this d |>.trans (by omega))] at hh
    exact hh.trans_eq (hH d)
  · exact prescribed_matrix_kernel_lower _ (fun i => e (u i))
      (fun i j => genericPrescribedMatrix_degree (K := K) (n := n) e (u i) j) hln.le d

end FD56
