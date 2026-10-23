/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoRowLifting

/-! The bounded second auxiliary relation and its actual polynomial left kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n]

def depthTwoBetaCoefficientDegree (d : ℕ) : m ⊕ m → ℕ :=
  Sum.elim (fun _ => d+2) (fun _ => d+1)

def boundedDepthTwoBetaMap (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :
    ((m → BoundedPoly K d) × (∀ i : m ⊕ m, BoundedPoly K (depthTwoBetaCoefficientDegree d i)))
      →ₗ[K] (n → K[X]) :=
  (boundedKernelMap (P * M * M).transpose d).comp (LinearMap.fst K _ _) -
    (weightedBoundedKernelMap (depthTwoStack P (P*M)).transpose
      (depthTwoBetaCoefficientDegree d)).comp (LinearMap.snd K _ _)

def boundedDepthTwoBetaKernel (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :=
  LinearMap.ker (boundedDepthTwoBetaMap M P d)

omit [Fintype r] [DecidableEq m] [DecidableEq n] in
theorem boundedDepthTwoBetaKernel_relation (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (d : ℕ) (z : boundedDepthTwoBetaKernel M P d) :
    (P*M*M).transpose *ᵥ (fun i => (z.val.1 i).val) =
      (depthTwoStack P (P*M)).transpose *ᵥ (fun i => (z.val.2 i).val) :=
  sub_eq_zero.mp z.property

omit [Fintype r] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem depthTwo_stack_transpose_mulVec (P Q : Matrix m n K[X]) (v : m ⊕ m → K[X]) :
    (depthTwoStack P Q).transpose *ᵥ v =
      P.transpose *ᵥ (fun i => v (Sum.inl i)) +
      Q.transpose *ᵥ (fun i => v (Sum.inr i)) := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.transpose_apply,
    depthTwoStack, Sum.elim_inl, Sum.elim_inr, Pi.add_apply]

omit [Fintype r] [DecidableEq m] [DecidableEq n] in
theorem boundedDepthTwoBetaKernel_split_relation (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (d : ℕ) (z : boundedDepthTwoBetaKernel M P d) :
    (P*M*M).transpose *ᵥ (fun i => (z.val.1 i).val) =
      P.transpose *ᵥ (fun i => (z.val.2 (Sum.inl i)).val) +
      (P*M).transpose *ᵥ (fun i => (z.val.2 (Sum.inr i)).val) := by
  rw [boundedDepthTwoBetaKernel_relation, depthTwo_stack_transpose_mulVec]

def depthTwoBetaKernelProjection (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M))))) (d : ℕ) :
    boundedDepthTwoBetaKernel M P d →ₗ[K] polynomialKernelAtDegree
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).transpose d where
  toFun z := ⟨z.val.1, by
    change (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).transpose *ᵥ
      (fun i => (z.val.1 i).val) = 0
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, boundedDepthTwoBetaKernel_relation,
      Matrix.mulVec_mulVec, ← Matrix.transpose_mul, polynomialKernelBasisMatrix_mul,
      Matrix.transpose_zero, Matrix.zero_mulVec]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype r] in
theorem depthTwoBetaKernelProjection_injective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M) * R = 1) (d : ℕ) :
    Function.Injective (depthTwoBetaKernelProjection M P B d) := by
  intro z w hzw
  have ht : z.val.1 = w.val.1 := congrArg Subtype.val hzw
  have hc : (depthTwoStack P (P*M)).transpose *ᵥ (fun i => (z.val.2 i).val) =
      (depthTwoStack P (P*M)).transpose *ᵥ (fun i => (w.val.2 i).val) := by
    rw [← boundedDepthTwoBetaKernel_relation M P d z,
      ← boundedDepthTwoBetaKernel_relation M P d w, ht]
  have hd := congrArg (fun x => R.transpose *ᵥ x) hc
  dsimp only at hd
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hR,
    Matrix.transpose_one, Matrix.one_mulVec, Matrix.one_mulVec] at hd
  apply Subtype.ext
  apply Prod.ext ht
  funext i
  exact Subtype.ext (congrFun hd i)

theorem depthTwoBetaKernelProjection_surjective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M) * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) (d : ℕ) :
    Function.Surjective (depthTwoBetaKernelProjection M P B d) := by
  intro y
  let T : Matrix Unit m K[X] := fun _ j => (y.val j).val
  let S : Matrix Unit n K[X] := T * P * M * M
  have hSV : S * polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B = 0 := by
    funext i k
    have hh := congrFun y.property k
    change ((P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).transpose *ᵥ
      (fun j => (y.val j).val)) k = 0 at hh
    have he : (T * (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B)) i k = 0 := by
      simpa only [T, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, mul_comm] using hh
    simpa only [S, Matrix.mul_assoc] using he
  have hS : DegreeBound S (d+3) := by
    simpa only [S, Nat.add_assoc] using degreeBound_mul
      (degreeBound_mul (degreeBound_mul
        (show DegreeBound T d from fun _ j => boundedPoly_degree d (y.val j)) hP) hM) hM
  obtain ⟨he,hd⟩ := depthTwo_stack_factor P (P*M) B R hR hP
    (degreeBound_mul hP hM) hlead S (d+3) hS hSV
  let D : Matrix Unit (m ⊕ m) K[X] := S * R
  have hD (j : m ⊕ m) : (D () j).natDegree ≤ depthTwoBetaCoefficientDegree d j := by
    change ((S * R) () j).natDegree ≤ depthTwoBetaCoefficientDegree d j
    rcases hd () j with hz | ⟨_,hb⟩
    · simp [D,hz]
    · cases j <;> simp only [depthTwoRowDegree,depthTwoBetaCoefficientDegree,
        Sum.elim_inl,Sum.elim_inr] at hb ⊢ <;> omega
  let c : ∀ j : m ⊕ m, BoundedPoly K (depthTwoBetaCoefficientDegree d j) :=
    fun j => boundedPolyOf (D () j) (hD j)
  have hz : (y.val,c) ∈ boundedDepthTwoBetaKernel M P d := by
    change (P*M*M).transpose *ᵥ (fun j => (y.val j).val) -
      (depthTwoStack P (P*M)).transpose *ᵥ (fun j => (c j).val) = 0
    apply sub_eq_zero.mpr
    funext x
    have hh := congrFun (congrFun he ()) x
    change S () x = (D * depthTwoStack P (P*M)) () x at hh
    simpa only [S, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, T, c, boundedPolyOf, mul_comm] using hh
  exact ⟨⟨(y.val,c),hz⟩,rfl⟩

def depthTwoBetaKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M) * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) (d : ℕ) :
    boundedDepthTwoBetaKernel M P d ≃ₗ[K] polynomialKernelAtDegree
      (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).transpose d :=
  LinearEquiv.ofBijective (depthTwoBetaKernelProjection M P B d)
    ⟨depthTwoBetaKernelProjection_injective M P B R hR d,
      depthTwoBetaKernelProjection_surjective M P B R hR hM hP hlead d⟩

theorem depthTwo_beta_kernel_finrank (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (depthTwoStack P (P*M)))))
    (R : Matrix n (m ⊕ m) K[X]) (hR : depthTwoStack P (P*M) * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P (P*M) i x).coeff (depthTwoRowDegree i)))) (d : ℕ) :
    Module.finrank K (boundedDepthTwoBetaKernel M P d) = Module.finrank K
      (polynomialKernelAtDegree
        (P*M*M*polynomialKernelBasisMatrix (depthTwoStack P (P*M)) B).transpose d) :=
  (depthTwoBetaKernelEquiv M P B R hR hM hP hlead d).finrank_eq

end FD56
