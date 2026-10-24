/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericActualDepthTwoStack
import FD56.Stabilizer.GenericMiddleRank
import FD56.Stabilizer.RegularWitness

/-! Generic terminal observability has full column rank at every depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K F n m : Type*} [Field K] [Field F]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
theorem exists_terminal_observability_witness
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m) :
    ∃ (M : Matrix n n K) (P : Matrix m n K),
      Function.Injective (observabilityMatrix M P (q+1)).mulVec := by
  classical
  let r := Fin (Fintype.card n-q*Fintype.card m)
  let a := Fin (Fintype.card m)
  let e : r ↪ a := (Function.Embedding.nonempty_of_card_le
    (show Fintype.card r ≤ Fintype.card a by simp [r,a]; nlinarith [Nat.sub_add_cancel hmn])).some
  let B : Matrix a r K := fun i j => if e j=i then 1 else 0
  have hB : Function.Injective B.mulVec := by
    intro v w h
    funext j
    have hh := congrFun h (e j)
    have hv (z : r → K) : (B *ᵥ z) (e j) = z j := by
      change (∑ k, (if e k=e j then (1 : K) else 0)*z k) = z j
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        have he : e k ≠ e j := fun he => hk (e.injective he)
        simp [he]
      · simp
    exact (hv v).symm.trans (hh.trans (hv w))
  obtain ⟨L,hL⟩ := matrix_left_inverse_of_injective B hB
  let M₀ := (glWitness (0 : Matrix r r K) B q).1
  let P₀ := (glWitness (0 : Matrix r r K) B q).2
  have hprofile := (glWitness_observability_profile (0 : Matrix r r K) B L hL q).2
  have hi : Function.Injective (observabilityMatrix M₀ P₀ (q+1)).mulVec := by
    change Function.Injective (Matrix.toLin' (observabilityMatrix M₀ P₀ (q+1)))
    apply LinearMap.ker_eq_bot.mp
    rw [observabilityMatrix_ker]
    exact Submodule.finrank_eq_zero.mp hprofile
  let ec : n ≃ blockIndex a r q := Fintype.equivOfCardEq (by
    rw [blockIndex_card]
    simp only [a,r,Fintype.card_fin]
    nlinarith [Nat.sub_add_cancel hmn])
  let er : m ≃ a := Fintype.equivFin m
  have hpow (k : ℕ) : (M₀.submatrix ec ec)^k = (M₀^k).submatrix ec ec := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,pow_succ,ih,Matrix.submatrix_mul_equiv]
  have he : observabilityMatrix (M₀.submatrix ec ec) (P₀.submatrix er ec) (q+1) =
      (observabilityMatrix M₀ P₀ (q+1)).submatrix (Equiv.prodCongr (Equiv.refl _) er) ec := by
    funext i x
    change ((P₀.submatrix er ec)*(M₀.submatrix ec ec)^i.1.val) i.2 x = _
    rw [hpow,Matrix.submatrix_mul_equiv]
    rfl
  refine ⟨M₀.submatrix ec ec,P₀.submatrix er ec,?_⟩
  rw [he]
  intro v w h
  rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv] at h
  have hh : (observabilityMatrix M₀ P₀ (q+1)) *ᵥ (v ∘ ec.symm) =
      (observabilityMatrix M₀ P₀ (q+1)) *ᵥ (w ∘ ec.symm) := by
    funext i
    simpa only [Function.comp_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,
      Equiv.apply_symm_apply,Prod.mk.eta] using congrFun h (i.1,er.symm i.2)
  have hv := hi hh
  funext j
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun hv (ec j)

theorem universal_terminal_observability_injective
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m)
    (φ : MvPolynomial (MatrixParameters n m) K →+* F) (hφ : Function.Injective φ) :
    Function.Injective (observabilityMatrix ((universalSquare K n m).map φ)
      ((universalRows K n m).map φ) (q+1)).mulVec := by
  obtain ⟨M,P,hi⟩ := exists_terminal_observability_witness (K := K) q hmn hnm
  have he := universal_pair_specialization M P
  have hw : Function.Injective
      ((observabilityMatrix (universalSquare K n m) (universalRows K n m) (q+1)).map
        (matrixSpecialization M P)).mulVec := by
    rw [observabilityMatrix_map,he.1,he.2]
    exact hi
  have hh := matrix_injective_of_specialization MvPolynomial.C (matrixSpecialization M P)
    (fun c => by simp [matrixSpecialization]) φ hφ _ hw
  rwa [observabilityMatrix_map] at hh

theorem generic_terminal_observability_zero_injective
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m) :
    Function.Injective ((observabilityMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) (q+1)).map (Polynomial.evalRingHom 0)).mulVec := by
  let φ := (Polynomial.evalRingHom (0 : AffineCoefficientField K (MatrixParameters n m))).comp
    (affineParameterMap K (MatrixParameters n m))
  have hφ : Function.Injective φ := by
    dsimp only [φ]
    rw [affineParameterMap_zero]
    exact (IsFractionRing.injective
      (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
      (AffineCoefficientField K (MatrixParameters n m))).comp
      (MvPolynomial.rename_injective (R := K)
        (Sum.inl : MatrixParameters n m → MatrixParameters n m ⊕ MatrixParameters n m)
        Sum.inl_injective)
  rw [observabilityMatrix_map]
  change Function.Injective (observabilityMatrix
    (((universalSquare K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0))
    (((universalRows K n m).map (affineParameterMap K _)).map (Polynomial.evalRingHom 0)) (q+1)).mulVec
  rw [Matrix.map_map,Matrix.map_map]
  exact universal_terminal_observability_injective q hmn hnm φ hφ

theorem generic_terminal_observability_injective
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m) :
    Function.Injective (observabilityMatrix (genericAffineSquare K n m)
      (genericAffineRows K n m) (q+1)).mulVec :=
  polynomial_matrix_injective_of_zero _ (generic_terminal_observability_zero_injective q hmn hnm)

omit [Fintype m] [DecidableEq m] in
theorem terminal_kernel_transfer_injective {r : Type*} [Fintype r]
    (q : ℕ) (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P q))))
    (hO : Function.Injective (observabilityMatrix M P (q+1)).mulVec) :
    Function.Injective (P*M^q*polynomialKernelBasisMatrix (observabilityMatrix M P q) B).mulVec := by
  let V := polynomialKernelBasisMatrix (observabilityMatrix M P q) B
  have hzero (i : Fin q) : P*M^i.val*V=0 := by
    funext x j
    exact congrFun (congrFun (polynomialKernelBasisMatrix_mul _ B) (i,x)) j
  intro c d h
  apply polynomialKernelBasisMatrix_injective _ B
  apply hO
  funext ix
  rcases ix with ⟨i,x⟩
  by_cases hi : i.val < q
  · change ((P*M^i.val) *ᵥ (V*ᵥ c)) x = ((P*M^i.val) *ᵥ (V*ᵥ d)) x
    rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hzero ⟨i.val,hi⟩,
      Matrix.zero_mulVec,Matrix.zero_mulVec]
  · have hiq : i.val=q := by omega
    change ((P*M^i.val) *ᵥ (V*ᵥ c)) x = ((P*M^i.val) *ᵥ (V*ᵥ d)) x
    rw [hiq,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]
    exact congrFun h x

theorem generic_terminal_kernel_transfer_injective {r : Type*} [Fintype r]
    (q : ℕ) (hmn : q*Fintype.card m ≤ Fintype.card n)
    (hnm : Fintype.card n ≤ (q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix (genericAffineSquare K n m)
        (genericAffineRows K n m) q)))) :
    Function.Injective (genericAffineRows K n m*(genericAffineSquare K n m)^q*
      polynomialKernelBasisMatrix _ B).mulVec :=
  terminal_kernel_transfer_injective q _ _ B
    (generic_terminal_observability_injective q hmn hnm)

end FD56
