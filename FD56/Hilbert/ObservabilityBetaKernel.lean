/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoBetaKernel
import FD56.Hilbert.ObservabilityGLNormalForm

/-! Bounded auxiliary relations at arbitrary observability depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m n r : Type*} [Field K] [Fintype m] [Fintype n] [Fintype r]
  [DecidableEq m] [DecidableEq n]
variable (q : ℕ)

def observabilityBetaCoefficientDegree (q d : ℕ) (i : Fin q × m) : ℕ :=
  d+q-i.1.val

def boundedObservabilityBetaMap (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :
    ((m → BoundedPoly K d) × (∀ i : Fin q × m, BoundedPoly K (observabilityBetaCoefficientDegree q d i)))
      →ₗ[K] (n → K[X]) :=
  (boundedKernelMap (P * M ^ q).transpose d).comp (LinearMap.fst K _ _) -
    (weightedBoundedKernelMap (observabilityMatrix M P q).transpose
      (observabilityBetaCoefficientDegree q d)).comp (LinearMap.snd K _ _)

def boundedObservabilityBetaKernel (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :=
  LinearMap.ker (boundedObservabilityBetaMap q M P d)

omit [Fintype r] [DecidableEq m] in
theorem boundedObservabilityBetaKernel_relation (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (d : ℕ) (z : boundedObservabilityBetaKernel q M P d) :
    (P*M^q).transpose *ᵥ (fun i => (z.val.1 i).val) =
      (observabilityMatrix M P q).transpose *ᵥ (fun i => (z.val.2 i).val) :=
  sub_eq_zero.mp z.property

def observabilityBetaKernelProjection (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q)))) (d : ℕ) :
    boundedObservabilityBetaKernel q M P d →ₗ[K] polynomialKernelAtDegree
      (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B).transpose d where
  toFun z := ⟨z.val.1, by
    change (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B).transpose *ᵥ
      (fun i => (z.val.1 i).val) = 0
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, boundedObservabilityBetaKernel_relation,
      Matrix.mulVec_mulVec, ← Matrix.transpose_mul, polynomialKernelBasisMatrix_mul,
      Matrix.transpose_zero, Matrix.zero_mulVec]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype r] in
theorem observabilityBetaKernelProjection_injective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q * R = 1) (d : ℕ) :
    Function.Injective (observabilityBetaKernelProjection q M P B d) := by
  intro z w hzw
  have ht : z.val.1 = w.val.1 := congrArg Subtype.val hzw
  have hc : (observabilityMatrix M P q).transpose *ᵥ (fun i => (z.val.2 i).val) =
      (observabilityMatrix M P q).transpose *ᵥ (fun i => (w.val.2 i).val) := by
    rw [← boundedObservabilityBetaKernel_relation q M P d z,
      ← boundedObservabilityBetaKernel_relation q M P d w, ht]
  have hd := congrArg (fun x => R.transpose *ᵥ x) hc
  dsimp only at hd
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hR,
    Matrix.transpose_one, Matrix.one_mulVec, Matrix.one_mulVec] at hd
  apply Subtype.ext
  apply Prod.ext ht
  funext i
  exact Subtype.ext (congrFun hd i)

theorem observabilityBetaKernelProjection_surjective (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P q i x).coeff (i.1.val+1)))) (d : ℕ) :
    Function.Surjective (observabilityBetaKernelProjection q M P B d) := by
  intro y
  let T : Matrix Unit m K[X] := fun _ j => (y.val j).val
  let S : Matrix Unit n K[X] := T * P * M ^ q
  have hSV : S * polynomialKernelBasisMatrix (observabilityMatrix M P q) B = 0 := by
    funext i k
    have hh := congrFun y.property k
    change ((P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B).transpose *ᵥ
      (fun j => (y.val j).val)) k = 0 at hh
    have he : (T * (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B)) i k = 0 := by
      simpa only [T, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, mul_comm] using hh
    simpa only [S, Matrix.mul_assoc] using he
  have hPM : DegreeBound (P*M^q) (q+1) := by
    simpa only [mul_one,Nat.add_comm] using degreeBound_mul hP (degreeBound_pow M 1 hM q)
  have hS : DegreeBound S (d+q+1) := by
    simpa only [S,Matrix.mul_assoc,Nat.add_assoc] using degreeBound_mul
      (show DegreeBound T d from fun _ j => boundedPoly_degree d (y.val j)) hPM
  have he := row_factor_through_of_kernel_basis (observabilityMatrix M P q) B R hR S hSV
  have hd := row_coordinates_degree_bound (observabilityMatrix M P q) (S*R)
    (fun i => i.1.val+1) (fun _ => d+q+1)
    (fun i j => (observability_polynomial_degree_top M P q hM hP i j).1) hlead
    (by rw [← he]; exact hS)
  let D : Matrix Unit (Fin q × m) K[X] := S * R
  have hD (j : Fin q × m) : (D () j).natDegree ≤ observabilityBetaCoefficientDegree q d j := by
    change ((S * R) () j).natDegree ≤ observabilityBetaCoefficientDegree q d j
    rcases hd () j with hz | ⟨_,hb⟩
    · simp [D,hz]
    · simp only [observabilityBetaCoefficientDegree] at hb ⊢
      omega
  let c : ∀ j : Fin q × m, BoundedPoly K (observabilityBetaCoefficientDegree q d j) :=
    fun j => boundedPolyOf (D () j) (hD j)
  have hz : (y.val,c) ∈ boundedObservabilityBetaKernel q M P d := by
    change (P*M^q).transpose *ᵥ (fun j => (y.val j).val) -
      (observabilityMatrix M P q).transpose *ᵥ (fun j => (c j).val) = 0
    apply sub_eq_zero.mpr
    funext x
    have hh := congrFun (congrFun he ()) x
    change S () x = (D * observabilityMatrix M P q) () x at hh
    simpa only [S, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, T, c, boundedPolyOf, mul_comm] using hh
  exact ⟨⟨(y.val,c),hz⟩,rfl⟩

def observabilityBetaKernelEquiv (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P q i x).coeff (i.1.val+1)))) (d : ℕ) :
    boundedObservabilityBetaKernel q M P d ≃ₗ[K] polynomialKernelAtDegree
      (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B).transpose d :=
  LinearEquiv.ofBijective (observabilityBetaKernelProjection q M P B d)
    ⟨observabilityBetaKernelProjection_injective q M P B R hR d,
      observabilityBetaKernelProjection_surjective q M P B R hR hM hP hlead d⟩

theorem observability_beta_kernel_finrank (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (R : Matrix n (Fin q × m) K[X]) (hR : observabilityMatrix M P q * R = 1)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (observabilityMatrix M P q i x).coeff (i.1.val+1)))) (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q M P d) = Module.finrank K
      (polynomialKernelAtDegree
        (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B).transpose d) :=
  (observabilityBetaKernelEquiv q M P B R hR hM hP hlead d).finrank_eq

end FD56
