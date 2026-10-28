/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerScalarObstruction

/-! Exact bounded scalar obstructions transported by a constant Kronecker
congruence. The coefficients are the transformed actual covector. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n ι : Type*} [Field K]
  [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def kroneckerScalarObstruction (e : ι → ℕ)
    (a : (Σ i, Fin (e i) ⊕ Fin (e i+1)) → K) (d : ℕ) :
    BoundedPoly K (d+1) →ₗ[K] ((Σ i, Fin (e i-(d+1))) → K) where
  toFun c r := ∑ s : Fin (d+2), (-1:K)^s.val*
    a ⟨r.1,Sum.inl ⟨r.2.val+s.val,by have := r.2.isLt; have := s.isLt; omega⟩⟩*
      c.val.coeff s.val
  map_add' c f := by ext r; simp [Polynomial.coeff_add,mul_add,Finset.sum_add_distrib]
  map_smul' a c := by ext r; simp [Polynomial.coeff_smul,Finset.mul_sum,mul_left_comm,mul_assoc]

theorem constant_congruence_scalar_forcing_iff
    (H : Matrix n n K[X]) (e : ι → ℕ)
    (T : Matrix n (Σ i, Fin (e i) ⊕ Fin (e i+1)) K)
    (S : Matrix (Σ i, Fin (e i) ⊕ Fin (e i+1)) n K)
    (hTS : T*S=1) (hST : S*T=1)
    (hcong : (T.map C).transpose*H*T.map C=
      Matrix.blockDiagonal' (fun i => kroneckerBlockPencil (K:=K) (e i)))
    (a : n → K) (ha : ∀ i j, (T.transpose *ᵥ a) ⟨i,Sum.inr j⟩=0)
    (d : ℕ) (c : BoundedPoly K (d+1)) :
    (∃ z : n → K[X], (∀ k, (z k).natDegree≤d) ∧
      H *ᵥ z=c.val • (fun k => C (a k)) ∧ (fun k => C (a k)) ⬝ᵥ z=0) ↔
      kroneckerScalarObstruction e (T.transpose *ᵥ a) d c=0 := by
  let b := T.transpose *ᵥ a
  have hbc : (fun k => C (b k))=(T.map C).transpose *ᵥ (fun k => C (a k)) := by
    ext k
    simp [b,Matrix.mulVec,dotProduct,map_sum,map_mul]
  have hTS' : T.map C*S.map C=1 := by rw [← Matrix.map_mul,hTS]; simp
  have hleft : (S.map C).transpose*(T.map C).transpose=1 := by
    rw [← Matrix.transpose_mul,hTS',Matrix.transpose_one]
  have hi : Function.Injective (T.map C).transpose.mulVec := by
    intro u v huv
    have h := congrArg (S.map C).transpose.mulVec huv
    simpa only [Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec] using h
  have hiff := kronecker_scalar_forcing_iff e b ha d c.val (boundedPoly_degree _ c)
  have hcrit : (∀ (i : ι) (r : Fin (e i-(d+1))),
      (∑ s : Fin (d+2), (-1:K)^s.val*b ⟨i,Sum.inl ⟨r.val+s.val,by
        have := r.isLt; have := s.isLt; omega⟩⟩*c.val.coeff s.val)=0) ↔
      kroneckerScalarObstruction e b d c=0 := by
    simp only [kroneckerScalarObstruction,LinearMap.coe_mk,AddHom.coe_mk,
      funext_iff,Pi.zero_apply]
    exact ⟨fun h ⟨i,r⟩ => h i r,fun h i r => h ⟨i,r⟩⟩
  rw [← hcrit,← hiff]
  constructor
  · rintro ⟨z,hz,hforce,hzero⟩
    have hrecover : T.map C *ᵥ (S.map C *ᵥ z)=z := by
      rw [Matrix.mulVec_mulVec,hTS',Matrix.one_mulVec]
    refine ⟨S.map C *ᵥ z,constant_mulVec_degree S z d hz,?_,?_⟩
    · rw [← hcong,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
        hrecover,
        hforce,Matrix.mulVec_smul,← hbc]
    · rw [hbc,dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,
        dotProduct_comm,Matrix.mulVec_mulVec,hTS',Matrix.one_mulVec]
      exact hzero
  · rintro ⟨z,hz,hforce,hzero⟩
    refine ⟨T.map C *ᵥ z,constant_mulVec_degree T z d hz,?_,?_⟩
    · apply hi
      rw [Matrix.mulVec_smul,← hbc]
      simpa only [← hcong,← Matrix.mulVec_mulVec] using hforce
    · rw [hbc,dotProduct_comm,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,dotProduct_comm] at hzero
      exact hzero

end FD56
