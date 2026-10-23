/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoRowLifting

/-! Affine row lifting through the kernel basis of a stack of row degrees one and two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K]
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq n]

def depthTwoAffineKernelCoordinates (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) :
    polynomialKernelAtDegree (polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose 1
      →ₗ[K] (m → K) where
  toFun z j := (∑ x, (z.val x).val * R x (Sum.inl j)).coeff 0
  map_add' z w := by
    funext j
    simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      Polynomial.coeff_add]
  map_smul' c z := by
    funext j
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum,
      Polynomial.coeff_smul]
    rfl

theorem depthTwoAffineKernelCoordinates_injective (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i)))) :
    Function.Injective (depthTwoAffineKernelCoordinates P Q B R) := by
  intro x y hxy
  suffices hz : x-y=0 by exact sub_eq_zero.mp hz
  let z := x-y
  have hz' : depthTwoAffineKernelCoordinates P Q B R z = 0 := by
    change depthTwoAffineKernelCoordinates P Q B R (x-y)=0
    exact ((depthTwoAffineKernelCoordinates P Q B R).map_sub x y).trans
      (by rw [hxy,sub_self])
  let S : Matrix Unit n K[X] := fun _ j => (z.val j).val
  have hS : DegreeBound S 1 := fun _ j => boundedPoly_degree 1 (z.val j)
  have hSV : S * polynomialKernelBasisMatrix (depthTwoStack P Q) B = 0 := by
    funext i j
    have hh := congrFun z.property j
    change ((polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose *ᵥ
      (fun x => (z.val x).val)) j = 0 at hh
    simpa only [S, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, mul_comm] using hh
  have he := depthTwo_affine_annihilator P Q B R hR hP hQ hlead S hS hSV
  have hcoeff (j : m) : ((S * R) () (Sum.inl j)).coeff 0 = 0 := by
    exact congrFun hz' j
  have hzero : S = 0 := by
    rw [he]
    funext i j
    cases i
    change (∑ k, C (((S * R) () (Sum.inl k)).coeff 0) * P k j) = 0
    simp only [hcoeff,map_zero,zero_mul,Finset.sum_const_zero]
  apply Subtype.ext
  funext j
  apply Subtype.ext
  exact congrFun (congrFun hzero ()) j

theorem depthTwo_affine_kernel_finrank_le (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i)))) :
    Module.finrank K (polynomialKernelAtDegree
      (polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose 1) ≤ Fintype.card m := by
  simpa only [Module.finrank_fintype_fun_eq_card] using
    LinearMap.finrank_le_finrank_of_injective
      (depthTwoAffineKernelCoordinates_injective P Q B R hR hP hQ hlead)

theorem depthTwo_affine_coefficient_surjective (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (α : r → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix (depthTwoStack P Q) B i j).natDegree ≤ α j)
    (hcard : Fintype.card m + ∑ j, (α j + 2) = 2 * Fintype.card n) :
    Function.Surjective (weightedCoefficientMatrix
      (polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose
      (fun _ => 1) (fun j => α j + 1)).mulVec := by
  let V := polynomialKernelBasisMatrix (depthTwoStack P Q) B
  have hb : ∀ i j, (V.transpose i j).natDegree + 1 ≤ α i + 1 :=
    fun i j => Nat.add_le_add_right (hV j i) 1
  let T := Matrix.toLin' (weightedCoefficientMatrix V.transpose (fun _ => 1)
    (fun j => α j + 1))
  have hk := depthTwo_affine_kernel_finrank_le P Q B R hR hP hQ hlead
  have hh := T.finrank_range_add_finrank_ker
  rw [weighted_coefficient_kernel_finrank V.transpose (fun _ => 1)
    (fun j => α j + 1) hb] at hh
  have hl := Submodule.finrank_le (LinearMap.range T)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hh hl
  change Function.Surjective T
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_fin]
  change Module.finrank K (polynomialKernelAtDegree V.transpose 1) ≤ _ at hk
  change Module.finrank K (LinearMap.range T) +
    Module.finrank K (polynomialKernelAtDegree V.transpose 1) = _ at hh
  simp only [Nat.add_assoc, Nat.reduceAdd] at hh hl ⊢
  omega

theorem depthTwo_affine_lift (P Q : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P Q))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P Q * R = 1)
    (hP : DegreeBound P 1) (hQ : DegreeBound Q 2)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))))
    (α : r → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix (depthTwoStack P Q) B i j).natDegree ≤ α j)
    (hcard : Fintype.card m + ∑ j, (α j + 2) = 2 * Fintype.card n)
    (w : r → K[X]) (hw : ∀ j, (w j).natDegree ≤ α j + 1) :
    ∃ s : n → K[X], (∀ j, (s j).natDegree ≤ 1) ∧
      (polynomialKernelBasisMatrix (depthTwoStack P Q) B).transpose *ᵥ s = w := by
  exact weighted_coefficient_surjective_lift _ (fun _ => 1) (fun j => α j + 1)
    (fun i j => Nat.add_le_add_right (hV j i) 1)
    (depthTwo_affine_coefficient_surjective P Q B R hR hP hQ hlead α hV hcard) w hw

end FD56
