/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaKernel
import FD56.Hilbert.WeightedCoefficients

/-! Finite coefficient equations for the auxiliary kernel at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R S K m n : Type*} [CommRing R] [CommRing S] [Field K]
  [Fintype n] [DecidableEq n]

def observabilityBetaDegrees (q d : ℕ) : m ⊕ (Fin q × m) → ℕ :=
  Sum.elim (fun _ => d) (observabilityBetaCoefficientDegree q d)

def observabilityBetaEquationMatrix (q : ℕ) (M : Matrix n n R[X])
    (P : Matrix m n R[X]) : Matrix n (m ⊕ (Fin q × m)) R[X] :=
  fun x => Sum.elim (fun i => (P*M^q) i x) (fun i => -(observabilityMatrix M P q i x))

def observabilityBetaCoefficientMatrix (q : ℕ) (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (d : ℕ) :
    Matrix (Σ _ : n, Fin (d+q+2))
      (Σ j : m ⊕ (Fin q × m), Fin (observabilityBetaDegrees q d j+1)) R :=
  weightedCoefficientMatrix (observabilityBetaEquationMatrix q M P)
    (observabilityBetaDegrees q d) (fun _ => d+q+1)

theorem observabilityBetaEquationMatrix_map (q : ℕ) (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (φ : R →+* S) :
    observabilityBetaEquationMatrix q (M.map (Polynomial.mapRingHom φ))
        (P.map (Polynomial.mapRingHom φ))=
      (observabilityBetaEquationMatrix q M P).map (Polynomial.mapRingHom φ) := by
  have hpow : (M^q).map (Polynomial.mapRingHom φ)=(M.map (Polynomial.mapRingHom φ))^q :=
    map_pow (Polynomial.mapRingHom φ).mapMatrix M q
  have he : (P*M^q).map (Polynomial.mapRingHom φ)=
      P.map (Polynomial.mapRingHom φ)*(M.map (Polynomial.mapRingHom φ))^q := by
    rw [Matrix.map_mul,hpow]
  have ho := observabilityMatrix_map (Polynomial.mapRingHom φ) M P q
  funext x j
  cases j with
  | inl i => exact (congrFun (congrFun he i) x).symm
  | inr i =>
    have hh := congrFun (congrFun ho i) x
    simpa only [observabilityBetaEquationMatrix,Sum.elim_inr,Matrix.map_apply,map_neg] using
      congrArg Neg.neg hh.symm

theorem observabilityBetaCoefficientMatrix_map (q : ℕ) (M : Matrix n n R[X])
    (P : Matrix m n R[X]) (d : ℕ) (φ : R →+* S) :
    observabilityBetaCoefficientMatrix q (M.map (Polynomial.mapRingHom φ))
        (P.map (Polynomial.mapRingHom φ)) d=
      (observabilityBetaCoefficientMatrix q M P d).map φ := by
  rw [observabilityBetaCoefficientMatrix,observabilityBetaEquationMatrix_map]
  funext i j
  simp only [observabilityBetaCoefficientMatrix,weightedCoefficientMatrix,Matrix.map_apply,
    ← Polynomial.coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  rfl

theorem observabilityBetaEquationMatrix_mulVec [Fintype m] (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (v : m ⊕ (Fin q × m) → K[X]) :
    observabilityBetaEquationMatrix q M P *ᵥ v=
      (P*M^q).transpose *ᵥ (fun i => v (Sum.inl i))-
        (observabilityMatrix M P q).transpose *ᵥ (fun i => v (Sum.inr i)) := by
  funext x
  simp only [observabilityBetaEquationMatrix,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Matrix.transpose_apply,Pi.sub_apply,neg_mul,Finset.sum_neg_distrib]
  abel

theorem observability_beta_weighted_degree_bound [Fintype m] (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    ∀ x j, (observabilityBetaEquationMatrix q M P x j).natDegree+
      observabilityBetaDegrees q d j≤d+q+1 := by
  intro x j
  cases j with
  | inl i =>
    have hh := degreeBound_mul hP (degreeBound_pow M 1 hM q) i x
    change ((P*M^q) i x).natDegree+d≤d+q+1
    simp only [mul_one] at hh
    omega
  | inr i =>
    have hh := (observability_polynomial_degree_top M P q hM hP i x).1
    change (-(observabilityMatrix M P q i x)).natDegree+(d+q-i.1.val)≤d+q+1
    rw [Polynomial.natDegree_neg]
    have := i.1.isLt
    omega

variable [Fintype m]

def observabilityBetaWeightedKernelEquiv (q : ℕ) (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (d : ℕ) :
    weightedPolynomialKernel (observabilityBetaEquationMatrix q M P) (observabilityBetaDegrees q d)
      ≃ₗ[K] boundedObservabilityBetaKernel q M P d where
  toFun z := ⟨(fun i => z.val (Sum.inl i),fun i => z.val (Sum.inr i)),by
    have hz := z.property
    change observabilityBetaEquationMatrix q M P *ᵥ (fun j => (z.val j).val)=0 at hz
    rw [observabilityBetaEquationMatrix_mulVec] at hz
    exact hz⟩
  invFun z := ⟨fun j => match j with
      | Sum.inl i => z.val.1 i
      | Sum.inr i => z.val.2 i,by
    change observabilityBetaEquationMatrix q M P *ᵥ _=0
    rw [observabilityBetaEquationMatrix_mulVec]
    exact z.property⟩
  left_inv z := by apply Subtype.ext; funext j; cases j <;> rfl
  right_inv z := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def observabilityBetaCoefficientKernelEquiv [DecidableEq m] (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    LinearMap.ker (Matrix.toLin' (observabilityBetaCoefficientMatrix q M P d))
      ≃ₗ[K] boundedObservabilityBetaKernel q M P d :=
  (weightedCoefficientKernelEquiv (observabilityBetaEquationMatrix q M P)
    (observabilityBetaDegrees q d) (fun _ => d+q+1)
    (observability_beta_weighted_degree_bound q M P hM hP d)).trans
      (observabilityBetaWeightedKernelEquiv q M P d)

theorem observability_beta_coefficient_kernel_finrank [DecidableEq m] (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (observabilityBetaCoefficientMatrix q M P d)))=
      Module.finrank K (boundedObservabilityBetaKernel q M P d) :=
  (observabilityBetaCoefficientKernelEquiv q M P hM hP d).finrank_eq

theorem depth_three_beta_kernel_lower [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ) :
    Fintype.card m*(4*d+10)-Fintype.card n*(d+5)≤
      Module.finrank K (boundedObservabilityBetaKernel 3 M P d) := by
  let T := Matrix.toLin' (observabilityBetaCoefficientMatrix 3 M P d)
  have hh := T.finrank_range_add_finrank_ker
  have hl := Submodule.finrank_le (LinearMap.range T)
  rw [observability_beta_coefficient_kernel_finrank 3 M P hM hP d] at hh
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_sigma,Fintype.card_fin,
    observabilityBetaDegrees,observabilityBetaCoefficientDegree,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type,Fin.sum_univ_succ] at hh hl
  simp only [Fin.val_zero,Fin.val_succ,Finset.univ_eq_empty,Finset.sum_empty,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,Nat.sub_zero,Nat.reduceAdd,add_zero] at hh hl
  have h1 : d+3-1=d+2 := by omega
  have h2 : d+3-2=d+1 := by omega
  rw [h1,h2] at hh
  have he : Fintype.card m*(4*d+10)=Fintype.card m*(d+1)+
      (Fintype.card m*(d+3+1)+(Fintype.card m*(d+2+1)+Fintype.card m*(d+1+1))) := by ring
  rw [he]
  change Module.finrank K (LinearMap.range T) +
    Module.finrank K (boundedObservabilityBetaKernel 3 M P d) = _ at hh
  simp only [Nat.add_assoc,Nat.reduceAdd] at hh hl ⊢
  omega

end FD56
