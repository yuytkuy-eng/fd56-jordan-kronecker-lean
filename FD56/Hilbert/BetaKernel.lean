/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelBasis
import FD56.LinearAlgebra.PolynomialLeading
import FD56.Hilbert.KernelDimension

/-! Polynomial row factorization and the bounded auxiliary beta relation. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K l m n r : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n]

theorem row_factor_through_of_kernel_basis (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (S : Matrix l n K[X])
    (hSV : S * polynomialKernelBasisMatrix P B = 0) : S = (S * R) * P := by
  have hann (v : LinearMap.ker (Matrix.toLin' P)) : S *ᵥ v.val = 0 := by
    have hv : polynomialKernelBasisMatrix P B *ᵥ (B.equivFun v) = v.val := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (B.equivFun.symm_apply_apply v)
    rw [← hv, Matrix.mulVec_mulVec, hSV, Matrix.zero_mulVec]
  have hPC : P * (1 - R * P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPR, Matrix.one_mul, sub_self]
  have hSC : S * (1 - R * P) = 0 := by
    apply Matrix.ext
    intro i j
    have hcol : P *ᵥ (fun x => (1 - R * P : Matrix n n K[X]) x j) = 0 := by
      funext k
      exact congrFun (congrFun hPC k) j
    exact congrFun (hann ⟨_, hcol⟩) i
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc] at hSC
  exact sub_eq_zero.mp hSC

omit [DecidableEq n] in
theorem row_factor_unique_of_right_inverse (P : Matrix m n K[X])
    (R : Matrix n m K[X]) (hPR : P * R = 1) (D E : Matrix l m K[X])
    (hDE : D * P = E * P) : D = E := by
  have h := congrArg (fun A : Matrix l n K[X] => A * R) hDE
  simpa only [Matrix.mul_assoc, hPR, Matrix.mul_one] using h

theorem beta_relation_of_kernel_basis (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (T : Matrix l m K[X])
    (hT : T * (P * M * polynomialKernelBasisMatrix P B) = 0) :
    T * P * M = (T * P * M * R) * P := by
  apply row_factor_through_of_kernel_basis P B R hPR
  simpa only [Matrix.mul_assoc] using hT

omit [DecidableEq m] [DecidableEq n] in
theorem beta_coefficient_degree (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i => (P i x).coeff 1)))
    (T D : Matrix l m K[X]) (d : ℕ) (hT : DegreeBound T d)
    (hrel : T * P * M = D * P) : DegreeBound D (d + 1) := by
  have hb : DegreeBound (D * P) (d + 2) := by
    rw [← hrel]
    simpa only [Nat.add_assoc] using degreeBound_mul (degreeBound_mul hT hP) hM
  have hc := row_coordinates_degree_bound P D (fun _ => 1) (fun _ => d + 2)
    hP hlead hb
  intro i j
  rcases hc i j with hz | ⟨_, hd⟩
  · simp [hz]
  · simpa using hd

def boundedBetaMap (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :
    ((m → BoundedPoly K d) × (m → BoundedPoly K (d + 1))) →ₗ[K] (n → K[X]) :=
  (boundedKernelMap (P * M).transpose d).comp (LinearMap.fst K _ _) -
    (boundedKernelMap P.transpose (d + 1)).comp (LinearMap.snd K _ _)

def boundedBetaKernel (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :
    Submodule K ((m → BoundedPoly K d) × (m → BoundedPoly K (d + 1))) :=
  LinearMap.ker (boundedBetaMap M P d)

omit [DecidableEq m] [DecidableEq n] in
theorem boundedBetaKernel_relation (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (d : ℕ) (z : boundedBetaKernel M P d) :
    (P * M).transpose *ᵥ (fun i => (z.val.1 i).val) =
      P.transpose *ᵥ (fun i => (z.val.2 i).val) := by
  exact sub_eq_zero.mp z.property

def betaKernelProjection (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P))) (d : ℕ) :
    boundedBetaKernel M P d →ₗ[K]
      polynomialKernelAtDegree (P * M * polynomialKernelBasisMatrix P B).transpose d where
  toFun z := ⟨z.val.1, by
    change (P * M * polynomialKernelBasisMatrix P B).transpose *ᵥ
      (fun i => (z.val.1 i).val) = 0
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, boundedBetaKernel_relation,
      Matrix.mulVec_mulVec, ← Matrix.transpose_mul, polynomialKernelBasisMatrix_mul,
      Matrix.transpose_zero, Matrix.zero_mulVec]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype r] in
theorem betaKernelProjection_injective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (d : ℕ) :
    Function.Injective (betaKernelProjection M P B d) := by
  intro z w hzw
  have ht : z.val.1 = w.val.1 := congrArg Subtype.val hzw
  have hc : P.transpose *ᵥ (fun i => (z.val.2 i).val) =
      P.transpose *ᵥ (fun i => (w.val.2 i).val) := by
    rw [← boundedBetaKernel_relation M P d z, ← boundedBetaKernel_relation M P d w, ht]
  have hd := congrArg (fun x => R.transpose *ᵥ x) hc
  dsimp only at hd
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    hPR, Matrix.transpose_one, Matrix.one_mulVec, Matrix.one_mulVec] at hd
  apply Subtype.ext
  apply Prod.ext ht
  funext i
  exact Subtype.ext (congrFun hd i)

theorem betaKernelProjection_surjective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i => (P i x).coeff 1))) (d : ℕ) :
    Function.Surjective (betaKernelProjection M P B d) := by
  intro y
  let T : Matrix Unit m K[X] := fun _ j => (y.val j).val
  have hTG : T * (P * M * polynomialKernelBasisMatrix P B) = 0 := by
    apply Matrix.ext
    intro i k
    have hh := congrFun y.property k
    change ((P * M * polynomialKernelBasisMatrix P B).transpose *ᵥ
      (fun j => (y.val j).val)) k = 0 at hh
    simpa only [T, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      mul_comm] using hh
  let D : Matrix Unit m K[X] := T * P * M * R
  have hrel : T * P * M = D * P := beta_relation_of_kernel_basis M P B R hPR T hTG
  have hDb : DegreeBound D (d + 1) := beta_coefficient_degree M P hM hP hlead T D d
    (fun _ j => boundedPoly_degree d (y.val j)) hrel
  let c : m → BoundedPoly K (d + 1) := fun j => boundedPolyOf (D () j) (hDb () j)
  have hz : (y.val, c) ∈ boundedBetaKernel M P d := by
    change (P * M).transpose *ᵥ (fun j => (y.val j).val) -
      P.transpose *ᵥ (fun j => (c j).val) = 0
    apply sub_eq_zero.mpr
    funext x
    have hh := congrFun (congrFun hrel ()) x
    change (T * P * M) () x = (D * P) () x at hh
    rw [Matrix.mul_assoc] at hh
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      T, c, boundedPolyOf, mul_comm] using hh
  exact ⟨⟨(y.val, c), hz⟩, rfl⟩

def betaKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i => (P i x).coeff 1))) (d : ℕ) :
    boundedBetaKernel M P d ≃ₗ[K]
      polynomialKernelAtDegree (P * M * polynomialKernelBasisMatrix P B).transpose d :=
  LinearEquiv.ofBijective (betaKernelProjection M P B d)
    ⟨betaKernelProjection_injective M P B R hPR d,
      betaKernelProjection_surjective M P B R hPR hM hP hlead d⟩

theorem beta_kernel_finrank (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i => (P i x).coeff 1))) (d : ℕ) :
    Module.finrank K (boundedBetaKernel M P d) =
      Module.finrank K
        (polynomialKernelAtDegree (P * M * polynomialKernelBasisMatrix P B).transpose d) :=
  (betaKernelEquiv M P B R hPR hM hP hlead d).finrank_eq

def betaKernelReindexEquiv {m₂ n₂ : Type*} [Fintype m₂] [Fintype n₂]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (er : m₂ ≃ m) (ec : n₂ ≃ n) (d : ℕ) :
    boundedBetaKernel (M.submatrix ec ec) (P.submatrix er ec) d ≃ₗ[K]
      boundedBetaKernel M P d where
  toFun z := ⟨(fun i => z.val.1 (er.symm i), fun i => z.val.2 (er.symm i)), by
    have hz := boundedBetaKernel_relation (M.submatrix ec ec) (P.submatrix er ec) d z
    rw [Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, Matrix.transpose_submatrix,
      Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv] at hz
    change (P * M).transpose *ᵥ (fun i => (z.val.1 (er.symm i)).val) -
      P.transpose *ᵥ (fun i => (z.val.2 (er.symm i)).val) = 0
    apply sub_eq_zero.mpr
    funext x
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using congrFun hz (ec.symm x)⟩
  invFun z := ⟨(fun i => z.val.1 (er i), fun i => z.val.2 (er i)), by
    change (P.submatrix er ec * M.submatrix ec ec).transpose *ᵥ
      (fun i => (z.val.1 (er i)).val) -
        (P.submatrix er ec).transpose *ᵥ (fun i => (z.val.2 (er i)).val) = 0
    apply sub_eq_zero.mpr
    rw [Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, Matrix.transpose_submatrix,
      Matrix.submatrix_mulVec_equiv, Matrix.submatrix_mulVec_equiv]
    funext x
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using
      congrFun (boundedBetaKernel_relation M P d z) (ec x)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> funext i <;> simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [DecidableEq m] [DecidableEq n] in
theorem beta_kernel_reindex_finrank {m₂ n₂ : Type*} [Fintype m₂] [Fintype n₂]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (er : m₂ ≃ m) (ec : n₂ ≃ n) (d : ℕ) :
    Module.finrank K (boundedBetaKernel (M.submatrix ec ec) (P.submatrix er ec) d) =
      Module.finrank K (boundedBetaKernel M P d) :=
  (betaKernelReindexEquiv M P er ec d).finrank_eq

end FD56
