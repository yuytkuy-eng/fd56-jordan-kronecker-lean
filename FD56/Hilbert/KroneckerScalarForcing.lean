/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RectangularLift
import FD56.Hilbert.KroneckerBlock
import FD56.Hilbert.PolynomialHyperplaneChart

/-! Bounded scalar forcing for a pure Kronecker pencil and a constant covector
which annihilates its polynomial kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxRecDepth 2048
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem kronecker_covector_large_coordinates_zero (e : ι → ℕ)
    (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K)
    (ha : ∀ v : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K[X],
      Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)) *ᵥ v=0 →
      (fun k => C (a k)) ⬝ᵥ v=0) :
    ∀ i j, a ⟨i,Sum.inr j⟩=0 := by
  intro i j
  let v : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K[X] :=
    fun k => if h : k.1=i then Sum.elim (fun _ => 0)
      (fun l => (-X : K[X])^l.val) (h ▸ k.2) else 0
  have hv : Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)) *ᵥ v=0 := by
    funext ⟨b,k⟩
    rw [blockDiagonal_mulVec]
    by_cases hb : b=i
    · subst b
      have hk : kroneckerBlockPencil (e i) *ᵥ
          Sum.elim (fun _ => (0 : K[X])) (fun l => (-X : K[X])^l.val)=0 := by
        apply (kroneckerBlockPencil_kernel_iff _ _).mpr
        refine ⟨rfl,?_⟩
        apply (bidiagonalPencil_kernel_iff _ _).mpr
        intro l
        simp
      simpa only [v,dif_pos rfl] using congrFun hk k
    · simp [v,hb,Matrix.mulVec,dotProduct]
  have hh := ha v hv
  have hs : (∑ l : Fin (e i+1), C (a ⟨i,Sum.inr l⟩)*(-X : K[X])^l.val)=0 := by
    simpa [dotProduct,Fintype.sum_sigma,Fintype.sum_sum_type,v] using hh
  have hp (l : Fin (e i+1)) : (-X : K[X])^l.val=C ((-1 : K)^l.val)*X^l.val := by
    rw [map_pow,← mul_pow]
    congr 1
    simp
  simp_rw [hp] at hs
  have hc := congrArg (fun p : K[X] => p.coeff j.val) hs
  simp only [Polynomial.finset_sum_coeff,coeff_C_mul,coeff_X_pow,coeff_zero] at hc
  simp only [Fin.val_inj,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,if_true] at hc
  have hc' : a ⟨i,Sum.inr j⟩*(-1 : K)^j.val=0 := by simpa using hc
  exact (mul_eq_zero.mp hc').resolve_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

theorem kronecker_scalar_forcing_lift (e : ι → ℕ)
    (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K)
    (ha : ∀ i j, a ⟨i,Sum.inr j⟩=0) (d : ℕ) (he : ∀ i, e i≤d+1)
    (c : K[X]) (hc : c.natDegree≤d+1) :
    ∃ z : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K[X],
      (∀ k, (z k).natDegree≤d) ∧
      Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)) *ᵥ z=
        c • (fun k => C (a k)) ∧ (fun k => C (a k)) ⬝ᵥ z=0 := by
  have hlift (i : ι) : ∃ z : Fin (e i+1) → K[X],
      (∀ j, (z j).natDegree≤d) ∧
      bidiagonalPencil (e i) *ᵥ z=fun j => c*C (a ⟨i,Sum.inl j⟩) := by
    apply polynomial_preimage_of_coefficient_surjective _ d (bidiagonalPencil_degree _)
      (bidiagonal_coefficient_surjective_of_length_le _ _ (he i))
    intro j
    exact (natDegree_mul_C_le _ _).trans hc
  choose z hz hmul using hlift
  refine ⟨fun k => Sum.elim (fun _ => 0) (z k.1) k.2,?_,?_,?_⟩
  · rintro ⟨i,j|j⟩
    · simp
    · exact hz i j
  · funext ⟨i,j⟩
    rw [blockDiagonal_mulVec]
    cases j with
    | inl j =>
      simpa [kroneckerBlockPencil,Matrix.fromBlocks_mulVec] using congrFun (hmul i) j
    | inr j => simp [kroneckerBlockPencil,Matrix.fromBlocks_mulVec,ha,Matrix.mulVec,dotProduct]
  · simp [dotProduct,Fintype.sum_sigma,Fintype.sum_sum_type,ha]

theorem constant_congruence_scalar_forcing_lift
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n K[X]) (e : ι → ℕ)
    (T : Matrix n (Σ i, Fin (e i) ⊕ Fin (e i+1)) K)
    (S : Matrix (Σ i, Fin (e i) ⊕ Fin (e i+1)) n K)
    (hTS : T*S=1) (hST : S*T=1)
    (hcong : (T.map C).transpose*H*T.map C=
      Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)))
    (a : n → K) (ha : ∀ v : n → K[X], H *ᵥ v=0 → (fun k => C (a k)) ⬝ᵥ v=0)
    (d : ℕ) (he : ∀ i, e i≤d+1) (c : K[X]) (hc : c.natDegree≤d+1) :
    ∃ z : n → K[X], (∀ k, (z k).natDegree≤d) ∧
      H *ᵥ z=c • (fun k => C (a k)) ∧ (fun k => C (a k)) ⬝ᵥ z=0 := by
  let b := T.transpose *ᵥ a
  have hbc : (fun k => C (b k))=(T.map C).transpose *ᵥ (fun k => C (a k)) := by
    funext k
    simp only [b,Matrix.mulVec,dotProduct,Matrix.transpose_apply,Matrix.map_apply,map_sum,map_mul]
  have hTS' : T.map C*S.map C=1 := by rw [← Matrix.map_mul,hTS]; simp
  have hleft : (S.map C).transpose*(T.map C).transpose=1 := by
    rw [← Matrix.transpose_mul,hTS',Matrix.transpose_one]
  have hi : Function.Injective (T.map C).transpose.mulVec := by
    intro v w hh
    have := congrArg (fun u => (S.map C).transpose *ᵥ u) hh
    simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec] using this
  have hb : ∀ v : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K[X],
      Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)) *ᵥ v=0 →
      (fun k => C (b k)) ⬝ᵥ v=0 := by
    intro v hv
    have hz : H *ᵥ (T.map C *ᵥ v)=0 := by
      apply hi
      rw [Matrix.mulVec_zero]
      simpa only [← hcong,← Matrix.mulVec_mulVec] using hv
    have ht := ha _ hz
    rw [hbc,dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm]
    exact ht
  obtain ⟨v,hv,hforce,hzero⟩ := kronecker_scalar_forcing_lift e b
    (kronecker_covector_large_coordinates_zero e b hb) d he c hc
  refine ⟨T.map C *ᵥ v,constant_mulVec_degree T v d hv,?_,?_⟩
  · apply hi
    rw [Matrix.mulVec_smul,← hbc]
    simpa only [← hcong,← Matrix.mulVec_mulVec] using hforce
  · rw [hbc,dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm] at hzero
    exact hzero

end FD56
