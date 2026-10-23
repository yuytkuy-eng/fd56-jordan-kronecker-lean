/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericPrescribedMatrix
import FD56.Hilbert.MixedScalarWitness
import FD56.Hilbert.MixedKernelBasis

/-! Simultaneous generic matrix ranks and high-row scalar obstructions. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 800000

section Coefficients
variable {R S L H m : Type*} [CommRing R] [CommRing S]
  [Fintype L] [Fintype H] [Fintype m]
  [DecidableEq L] [DecidableEq H] [DecidableEq m]

def mixedScalarCoefficientMatrix (G : Matrix m (L ⊕ H) R[X]) (b t : ℕ) (f : Fin t → ℕ) :
    Matrix ((H × (L ⊕ H) × Fin (b+1)) ⊕ Fin t) ((H × m) ⊕ Fin (b+1)) R :=
  fun i j => match i, j with
  | Sum.inl (h, c, k), Sum.inl (h', x) => if h = h' then (G x c).coeff k.val else 0
  | Sum.inl (h, c, k), Sum.inr l => if Sum.inr h = c ∧ l = k then 1 else 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr k, Sum.inr l => if l.val = f k then 1 else 0

omit [Fintype L] [Fintype H] [Fintype m] [DecidableEq m] in
theorem mixedScalarCoefficientMatrix_map (G : Matrix m (L ⊕ H) R[X])
    (b t : ℕ) (f : Fin t → ℕ) (φ : R →+* S) :
    (mixedScalarCoefficientMatrix G b t f).map φ =
      mixedScalarCoefficientMatrix (G.map (Polynomial.mapRingHom φ)) b t f := by
  funext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => dsimp [mixedScalarCoefficientMatrix, Matrix.map]; split_ifs <;> simp_all
    | inr j => dsimp [mixedScalarCoefficientMatrix, Matrix.map]; split_ifs <;> simp_all
  | inr i =>
    cases j <;> dsimp [mixedScalarCoefficientMatrix, Matrix.map]
    · simp
    · split_ifs <;> simp_all

def mixedScalarInputMatrix (b : ℕ) (z : (H × m) ⊕ Fin (b+1) → R) : Matrix H m R :=
  fun i x => z (Sum.inl (i,x))

def mixedScalarInputPoly (b : ℕ) (z : (H × m) ⊕ Fin (b+1) → R) : R[X] := by
  classical
  exact Polynomial.ofFn (b+1) (fun k => z (Sum.inr k))

def mixedScalarHighIdentity : Matrix H (L ⊕ H) R[X] :=
  fun i j => if Sum.inr i = j then 1 else 0

omit [Fintype L] [DecidableEq m] in
theorem mixedScalarCoefficientMatrix_mulVec_main (G : Matrix m (L ⊕ H) R[X])
    (b t : ℕ) (f : Fin t → ℕ) (z : (H × m) ⊕ Fin (b+1) → R)
    (i : H) (j : L ⊕ H) (k : Fin (b+1)) :
    (mixedScalarCoefficientMatrix G b t f *ᵥ z) (Sum.inl (i,j,k)) =
      (((mixedScalarInputMatrix b z).map C * G +
        mixedScalarInputPoly b z • (mixedScalarHighIdentity : Matrix H (L ⊕ H) R[X])) i j).coeff k.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    mixedScalarCoefficientMatrix, Fintype.sum_prod_type, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.add_apply, Polynomial.coeff_add,
    Matrix.mul_apply, Polynomial.finset_sum_coeff, Matrix.map_apply,
    mixedScalarInputMatrix, Polynomial.coeff_C_mul, Matrix.smul_apply,
    smul_eq_mul, mixedScalarInputPoly, mixedScalarHighIdentity]
  by_cases hij : Sum.inr i = j
  · simp [hij, Polynomial.ofFn_coeff_eq_val_of_lt _ k.isLt, mul_comm]
  · simp [hij, mul_comm]

omit [Fintype L] [DecidableEq m] in
theorem mixedScalarCoefficientMatrix_mulVec_tail (G : Matrix m (L ⊕ H) R[X])
    (b t : ℕ) (f : Fin t → ℕ) (z : (H × m) ⊕ Fin (b+1) → R)
    (k : Fin t) (hk : f k ≤ b) :
    (mixedScalarCoefficientMatrix G b t f *ᵥ z) (Sum.inr k) =
      (mixedScalarInputPoly b z).coeff (f k) := by
  classical
  let l : Fin (b+1) := ⟨f k, by omega⟩
  have he : ∀ j : Fin (b+1), j.val = f k ↔ j = l := by
    intro j
    exact (@Fin.ext_iff _ j l).symm
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    mixedScalarCoefficientMatrix, he, mixedScalarInputPoly,
    Polynomial.ofFn_coeff_eq_val_of_lt _ (show f k < b+1 by omega), l]

end Coefficients

section Injectivity
variable {K L H m : Type*} [Field K] [Fintype L] [Fintype H] [Fintype m]
  [DecidableEq L] [DecidableEq H] [DecidableEq m]

omit [Fintype L] in
theorem mixedScalarCoefficientMatrix_injective_of_obstruction
    (G : Matrix m (L ⊕ H) K[X]) (b t : ℕ) (f : Fin t → ℕ)
    (hG : DegreeBound G b) (hf : ∀ k, f k ≤ b)
    (hz : ∀ (E : Matrix H m K) (c : K[X]),
      E.map C * G = (-c) • (mixedScalarHighIdentity : Matrix H (L ⊕ H) K[X]) →
      (∀ k, c.coeff (f k) = 0) → E = 0 ∧ c = 0) :
    Function.Injective (mixedScalarCoefficientMatrix G b t f).mulVec := by
  classical
  apply (injective_iff_map_eq_zero (Matrix.toLin' _)).mpr
  intro z hz0
  let E := mixedScalarInputMatrix b z
  let c := mixedScalarInputPoly b z
  have hE : DegreeBound (E.map C) 0 := by intro i j; simp
  have hc : c.natDegree ≤ b := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (show 1 ≤ b+1 by omega) _)
  have hr : E.map C * G = (-c) • (mixedScalarHighIdentity : Matrix H (L ⊕ H) K[X]) := by
    rw [neg_smul]
    apply eq_neg_iff_add_eq_zero.mpr
    funext i j
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ b
    · have h := congrFun hz0 (Sum.inl (i,j,⟨k, by omega⟩))
      change (mixedScalarCoefficientMatrix G b t f *ᵥ z) _ = 0 at h
      rw [mixedScalarCoefficientMatrix_mulVec_main] at h
      simpa only [E, c, neg_smul, neg_neg, Pi.add_apply, Pi.zero_apply, coeff_zero] using h
    · have hdeg : ((E.map C * G + c •
          (mixedScalarHighIdentity : Matrix H (L ⊕ H) K[X])) i j).natDegree ≤ b := by
        apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · simpa using degreeBound_mul hE hG i j
        · by_cases hij : Sum.inr i = j <;> simp [mixedScalarHighIdentity, hij, hc]
      simpa [neg_smul] using Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
  have ht : ∀ k, c.coeff (f k) = 0 := by
    intro k
    have h := congrFun hz0 (Sum.inr k)
    change (mixedScalarCoefficientMatrix G b t f *ᵥ z) _ = 0 at h
    rw [mixedScalarCoefficientMatrix_mulVec_tail G b t f z k (hf k)] at h
    exact h
  obtain ⟨hEz, hcz⟩ := hz E c hr ht
  funext j
  cases j with
  | inl j => exact congrFun (congrFun hEz j.1) j.2
  | inr j =>
    have h := congrArg (fun p : K[X] => p.coeff j.val) hcz
    simpa [c, mixedScalarInputPoly, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt] using h

end Injectivity

section Obstruction
variable {K L H m : Type*} [Field K] [Fintype L] [Fintype H] [Fintype m]
  [DecidableEq L] [DecidableEq H] [DecidableEq m]

omit [Fintype L] [DecidableEq m] in
theorem mixedScalarCoefficientMatrix_obstruction_of_injective
    (G : Matrix m (L ⊕ H) K[X]) (b t : ℕ) (f : Fin t → ℕ)
    (hf : ∀ k, f k ≤ b)
    (hi : Function.Injective (mixedScalarCoefficientMatrix G b t f).mulVec)
    (E : Matrix H m K) (c : K[X]) (hc : c.natDegree ≤ b)
    (hr : E.map C * G = (-c) • (mixedScalarHighIdentity : Matrix H (L ⊕ H) K[X]))
    (ht : ∀ k, c.coeff (f k) = 0) : E = 0 ∧ c = 0 := by
  classical
  let z : (H × m) ⊕ Fin (b+1) → K :=
    Sum.elim (fun i => E i.1 i.2) (fun k => c.coeff k.val)
  have hE : mixedScalarInputMatrix b z = E := rfl
  have hC : mixedScalarInputPoly b z = c :=
    Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have hz : mixedScalarCoefficientMatrix G b t f *ᵥ z = 0 := by
    funext i
    cases i with
    | inl i =>
      rw [mixedScalarCoefficientMatrix_mulVec_main, hE, hC, hr, neg_smul, neg_add_cancel]
      rfl
    | inr i =>
      rw [mixedScalarCoefficientMatrix_mulVec_tail G b t f z i (hf i), hC, ht]
      rfl
  have hz0 : z = 0 := hi (hz.trans (Matrix.mulVec_zero _).symm)
  constructor
  · funext i j
    exact congrFun hz0 (Sum.inl (i,j))
  · rw [← hC, hz0]
    simp [mixedScalarInputPoly, Polynomial.ofFn_eq_sum_monomial]

end Obstruction

abbrev MixedWitnessField (K : Type*) [Field K] (a u v : ℕ) :=
  PrescribedMatrixField K (MixedScalarRows a (Fin u) (Fin v))
    (fun j => mixedKernelDegree a u v j + 2)

def genericMixedWitness (K : Type*) [Field K] (a u v : ℕ) :
    Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v)
      (MixedWitnessField K a u v)[X] :=
  (genericPrescribedMatrix K (MixedScalarRows a (Fin u) (Fin v))
    (fun j => mixedKernelDegree a u v j + 2)).transpose

variable {K : Type*} [Field K]

theorem genericMixedWitness_degree (a u v : ℕ) (x : MixedScalarRows a (Fin u) (Fin v))
    (j : Fin u ⊕ Fin v) :
    (genericMixedWitness K a u v x j).natDegree ≤ mixedKernelDegree a u v j + 2 :=
  genericPrescribedMatrix_degree _ j x

theorem genericMixedWitness_scalar_coefficient_injective (a u v : ℕ)
    (ha : 0 < a) (hv : 0 < v) :
    Function.Injective (mixedScalarCoefficientMatrix (genericMixedWitness K a u v)
      (a+3) ((a+1) - 3 * (v * (u+v) - 1))
      (fun l => 3 * (v * (u+v) - 1) + l.val)).mulVec := by
  classical
  let e := fun j => mixedKernelDegree a u v j + 2
  obtain ⟨W, hW, _, hzero⟩ := exists_mixed_scalar_witness (K := K) a u v ha hv
  have hWe : ∀ j x, (W.transpose j x).natDegree ≤ e j := by
    intro j x
    have hh := hW x j
    cases j <;> simpa [e, mixedKernelDegree, mixedColumnShift] using hh
  have hWb : DegreeBound W (a+3) := by
    intro x j
    have hh := hWe j x
    cases j <;> simp only [e, mixedKernelDegree_inl, mixedKernelDegree_inr,
      Matrix.transpose_apply] at hh <;> omega
  let ψ := prescribedMatrixSpecialization e (RingHom.id K) W.transpose
  let φ := algebraMap
    (MvPolynomial (PrescribedMatrixParameters (MixedScalarRows a (Fin u) (Fin v)) e) K)
    (MixedWitnessField K a u v)
  let U := (universalPrescribedMatrix K (MixedScalarRows a (Fin u) (Fin v)) e).transpose
  let A := mixedScalarCoefficientMatrix U (a+3) ((a+1)-3*(v*(u+v)-1))
    (fun l => 3*(v*(u+v)-1)+l.val)
  have hU : U.map (Polynomial.mapRingHom ψ) = W := by
    change (universalPrescribedMatrix K _ e).transpose.map _ = _
    rw [Matrix.transpose_map, universalPrescribedMatrix_specialization e (RingHom.id K)
      W.transpose hWe, Matrix.transpose_transpose]
  have hAe : A.map ψ = mixedScalarCoefficientMatrix W (a+3) ((a+1)-3*(v*(u+v)-1))
      (fun l => 3*(v*(u+v)-1)+l.val) := by
    dsimp only [A]
    rw [mixedScalarCoefficientMatrix_map, hU]
  have hAg : A.map φ = mixedScalarCoefficientMatrix (genericMixedWitness K a u v)
      (a+3) ((a+1)-3*(v*(u+v)-1)) (fun l => 3*(v*(u+v)-1)+l.val) := by
    dsimp only [A]
    rw [mixedScalarCoefficientMatrix_map]
    rfl
  rw [← hAg]
  apply matrix_injective_of_field_specialization ψ φ (IsFractionRing.injective _ _) A
  rw [hAe]
  apply mixedScalarCoefficientMatrix_injective_of_obstruction _ _ _ _ hWb
    (fun l => by have := l.isLt; omega)
  exact hzero

theorem genericMixedWitness_scalar_obstruction (a u v : ℕ) (ha : 0 < a) (hv : 0 < v)
    (E : Matrix (Fin v) (MixedScalarRows a (Fin u) (Fin v)) (MixedWitnessField K a u v))
    (c : (MixedWitnessField K a u v)[X]) (hc : c.natDegree ≤ a+3)
    (hr : E.map C * genericMixedWitness K a u v = (-c) •
      (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K a u v)[X]))
    (ht : ∀ l : Fin ((a+1)-3*(v*(u+v)-1)), c.coeff (3*(v*(u+v)-1)+l.val) = 0) :
    E = 0 ∧ c = 0 := by
  apply mixedScalarCoefficientMatrix_obstruction_of_injective
    (genericMixedWitness K a u v) (a+3) ((a+1)-3*(v*(u+v)-1))
    (fun l => 3*(v*(u+v)-1)+l.val) _
    (genericMixedWitness_scalar_coefficient_injective (K := K) a u v ha hv) E c hc hr ht
  intro l
  change 3*(v*(u+v)-1)+l.val ≤ a+3
  have := l.isLt
  omega

theorem genericMixedWitness_kernel_hilbert (a u v : ℕ)
    (hm : u+v < a*(u+v)+v) (d : ℕ) :
    Module.finrank (MixedWitnessField K a u v)
      (polynomialKernelAtDegree (genericMixedWitness K a u v).transpose d) =
      (a*(u+v)+v-(u+v))*(d+1) - (a*(u+v)+v+2*(u+v)) := by
  have hcard : Fintype.card (MixedScalarRows a (Fin u) (Fin v)) = a*(u+v)+v := by
    simp only [MixedScalarRows, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  have hh := generic_prescribed_kernel_hilbert (K := K)
    (n := MixedScalarRows a (Fin u) (Fin v)) (fun j => mixedKernelDegree a u v j+2)
    (by simpa [hcard] using hm) d
  have hsum : (∑ j : Fin u ⊕ Fin v, (mixedKernelDegree a u v j+2)) =
      a*(u+v)+v+2*(u+v) := by
    simp only [Fintype.sum_sum_type, mixedKernelDegree_inl, mixedKernelDegree_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  simpa only [genericMixedWitness, Matrix.transpose_transpose, hcard,
    Fintype.card_sum, Fintype.card_fin, hsum] using hh

theorem genericMixedWitness_injective (a u v : ℕ) (ha : 0 < a) (hv : 0 < v) :
    Function.Injective (genericMixedWitness K a u v).mulVec := by
  classical
  let e := fun j => mixedKernelDegree a u v j + 2
  obtain ⟨W, hW, _, hW0, _⟩ := exists_mixed_scalar_witness_eval_zero (K := K) a u v ha hv
  have hWe : ∀ j x, (W.transpose j x).natDegree ≤ e j := by
    intro j x
    have hh := hW x j
    cases j <;> simpa [e, mixedKernelDegree, mixedColumnShift] using hh
  let ψ := prescribedMatrixSpecialization e (RingHom.id K) W.transpose
  let φ := algebraMap
    (MvPolynomial (PrescribedMatrixParameters (MixedScalarRows a (Fin u) (Fin v)) e) K)
    (MixedWitnessField K a u v)
  let U := (universalPrescribedMatrix K (MixedScalarRows a (Fin u) (Fin v)) e).transpose
  let A : Matrix (MixedScalarRows a (Fin u) (Fin v)) (Fin u ⊕ Fin v)
      (MvPolynomial (PrescribedMatrixParameters (MixedScalarRows a (Fin u) (Fin v)) e) K) :=
    fun x j => (U x j).coeff 0
  have hU : U.map (Polynomial.mapRingHom ψ) = W := by
    change (universalPrescribedMatrix K _ e).transpose.map _ = _
    rw [Matrix.transpose_map, universalPrescribedMatrix_specialization e (RingHom.id K)
      W.transpose hWe, Matrix.transpose_transpose]
  have hAe : A.map ψ = W.map (Polynomial.evalRingHom 0) := by
    funext x j
    have hh := congrArg (fun p : K[X] => p.coeff 0) (congrFun (congrFun hU x) j)
    simpa only [A, Matrix.map_apply, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
      Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero] using hh
  have hAg : A.map φ = (genericMixedWitness K a u v).map (Polynomial.evalRingHom 0) := by
    funext x j
    change φ ((U x j).coeff 0) = Polynomial.eval 0 ((U x j).map φ)
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
  apply polynomial_matrix_injective_of_zero
  rw [← hAg]
  apply matrix_injective_of_field_specialization ψ φ (IsFractionRing.injective _ _) A
  rw [hAe]
  exact hW0

end FD56
