/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoBetaKernel
import FD56.Hilbert.WeightedCoefficients

/-! Finite coefficient equations and the dimension bound for depth-two beta relations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R S K m n : Type*} [CommRing R] [CommRing S] [Field K]

def depthTwoBetaDegrees {m : Type*} (d : ℕ) : m ⊕ (m ⊕ m) → ℕ :=
  Sum.elim (fun _ => d) (depthTwoBetaCoefficientDegree d)

def depthTwoBetaEquationMatrix [Fintype n] (M : Matrix n n R[X])
    (P : Matrix m n R[X]) : Matrix n (m ⊕ (m ⊕ m)) R[X] :=
  fun x => Sum.elim (fun i => (P*M*M) i x)
    (Sum.elim (fun i => -P i x) (fun i => -(P*M) i x))

def depthTwoBetaCoefficientMatrix [Fintype n] (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (d : ℕ) :
    Matrix (Σ _ : n, Fin (d+3+1))
      (Σ j : m ⊕ (m ⊕ m), Fin (depthTwoBetaDegrees d j+1)) R :=
  weightedCoefficientMatrix (depthTwoBetaEquationMatrix M P)
    (depthTwoBetaDegrees d) (fun _ => d+3)

theorem depthTwoBetaEquationMatrix_map [Fintype n] (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (φ : R →+* S) :
    depthTwoBetaEquationMatrix (M.map (Polynomial.mapRingHom φ))
        (P.map (Polynomial.mapRingHom φ)) =
      (depthTwoBetaEquationMatrix M P).map (Polynomial.mapRingHom φ) := by
  funext x j
  cases j with
  | inl i =>
    change ((P.map (Polynomial.mapRingHom φ)) * (M.map (Polynomial.mapRingHom φ)) *
      (M.map (Polynomial.mapRingHom φ))) i x = _
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  | inr i =>
    cases i with
    | inl i => simp [depthTwoBetaEquationMatrix]
    | inr i =>
      change -((P.map (Polynomial.mapRingHom φ)) * (M.map (Polynomial.mapRingHom φ))) i x = _
      rw [← Matrix.map_mul]
      simp [depthTwoBetaEquationMatrix]

theorem depthTwoBetaCoefficientMatrix_map [Fintype n] (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (d : ℕ) (φ : R →+* S) :
    depthTwoBetaCoefficientMatrix (M.map (Polynomial.mapRingHom φ))
        (P.map (Polynomial.mapRingHom φ)) d =
      (depthTwoBetaCoefficientMatrix M P d).map φ := by
  rw [depthTwoBetaCoefficientMatrix, depthTwoBetaEquationMatrix_map]
  funext i j
  simp [weightedCoefficientMatrix, depthTwoBetaCoefficientMatrix,
    ← Polynomial.coeff_map, Polynomial.map_mul]

theorem depthTwoBetaEquationMatrix_mulVec [Fintype m] [Fintype n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (v : m ⊕ (m ⊕ m) → K[X]) :
    depthTwoBetaEquationMatrix M P *ᵥ v =
      (P*M*M).transpose *ᵥ (fun i => v (Sum.inl i)) -
        (depthTwoStack P (P*M)).transpose *ᵥ (fun i => v (Sum.inr i)) := by
  funext x
  simp only [depthTwoBetaEquationMatrix, depthTwoStack, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.transpose_apply,
    Pi.sub_apply, neg_mul, Finset.sum_neg_distrib]
  abel

theorem depthTwo_beta_weighted_degree_bound [Fintype n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    ∀ x j, (depthTwoBetaEquationMatrix M P x j).natDegree +
      depthTwoBetaDegrees d j ≤ d+3 := by
  intro x j
  cases j with
  | inl i =>
    have hh := degreeBound_mul (degreeBound_mul hP hM) hM i x
    change ((P*M*M) i x).natDegree+d ≤ d+3
    omega
  | inr j =>
    cases j with
    | inl i =>
      change (-P i x).natDegree+(d+2) ≤ d+3
      rw [Polynomial.natDegree_neg]
      have := hP i x
      omega
    | inr i =>
      change (-(P*M) i x).natDegree+(d+1) ≤ d+3
      rw [Polynomial.natDegree_neg]
      have := degreeBound_mul hP hM i x
      omega

variable [Fintype m] [Fintype n]

def depthTwoBetaWeightedKernelEquiv (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (d : ℕ) :
    weightedPolynomialKernel (depthTwoBetaEquationMatrix M P) (depthTwoBetaDegrees d)
      ≃ₗ[K] boundedDepthTwoBetaKernel M P d where
  toFun z := ⟨(fun i => z.val (Sum.inl i), fun i => z.val (Sum.inr i)), by
    have hz := z.property
    change depthTwoBetaEquationMatrix M P *ᵥ (fun j => (z.val j).val) = 0 at hz
    rw [depthTwoBetaEquationMatrix_mulVec] at hz
    exact hz⟩
  invFun z := ⟨fun j => match j with
      | Sum.inl i => z.val.1 i
      | Sum.inr i => z.val.2 i, by
    change depthTwoBetaEquationMatrix M P *ᵥ _ = 0
    rw [depthTwoBetaEquationMatrix_mulVec]
    exact z.property⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    cases j <;> rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def depthTwoBetaCoefficientKernelEquiv [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    LinearMap.ker (Matrix.toLin' (depthTwoBetaCoefficientMatrix M P d))
      ≃ₗ[K] boundedDepthTwoBetaKernel M P d :=
  (weightedCoefficientKernelEquiv (depthTwoBetaEquationMatrix M P)
    (depthTwoBetaDegrees d) (fun _ => d+3)
    (depthTwo_beta_weighted_degree_bound M P hM hP d)).trans
      (depthTwoBetaWeightedKernelEquiv M P d)

theorem depthTwo_beta_coefficient_kernel_finrank [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (depthTwoBetaCoefficientMatrix M P d))) =
      Module.finrank K (boundedDepthTwoBetaKernel M P d) :=
  (depthTwoBetaCoefficientKernelEquiv M P hM hP d).finrank_eq

theorem depthTwo_beta_kernel_lower [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Fintype.card m*(3*d+6)-Fintype.card n*(d+4) ≤
      Module.finrank K (boundedDepthTwoBetaKernel M P d) := by
  let T := Matrix.toLin' (depthTwoBetaCoefficientMatrix M P d)
  have hh := T.finrank_range_add_finrank_ker
  have hl := Submodule.finrank_le (LinearMap.range T)
  rw [depthTwo_beta_coefficient_kernel_finrank M P hM hP d] at hh
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
    Fintype.card_fin, depthTwoBetaDegrees, depthTwoBetaCoefficientDegree,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hh hl
  have he : Fintype.card m*(3*d+6) = Fintype.card m*(d+1) +
      (Fintype.card m*(d+2+1)+Fintype.card m*(d+1+1)) := by ring
  rw [he]
  change Module.finrank K (LinearMap.range T) +
    Module.finrank K (boundedDepthTwoBetaKernel M P d) = _ at hh
  simp only [Nat.add_assoc,Nat.reduceAdd] at hh hl ⊢
  omega

end FD56
