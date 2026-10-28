/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Bidiagonal
import FD56.Hilbert.Coefficients

/-! Exact bounded-image obstructions for a rectangular Kronecker block.
For scalar right-hand sides the obstruction coefficients form a signed
Hankel matrix of the actual constant forcing covector. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K]

private theorem coefficient_telescope (v : ℕ → K[X]) (n : ℕ) :
    (∑ s ∈ Finset.range (n+1), (-1:K)^s*(X*v s+v (s+1)).coeff s)=
      (-1:K)^n*(v (n+1)).coeff n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    simp only [Polynomial.coeff_add,Polynomial.coeff_X_mul,pow_succ]
    ring

def bidiagonalObstructionMap (m d : ℕ) :
    (Fin m × Fin (d+2) → K) →ₗ[K] (Fin (m-(d+1)) → K) where
  toFun g r := ∑ s : Fin (d+2), (-1:K)^s.val*g (⟨r.val+s.val,by
    have := r.isLt; have := s.isLt; omega⟩,s)
  map_add' g h := by ext r; simp [mul_add,Finset.sum_add_distrib]
  map_smul' a g := by ext r; simp [Finset.mul_sum,mul_left_comm]

theorem bidiagonalObstructionMap_surjective (m d : ℕ) :
    Function.Surjective (bidiagonalObstructionMap (K:=K) m d) := by
  intro y
  let g : Fin m × Fin (d+2) → K := fun j =>
    if j.2=0 then if h : j.1.val<m-(d+1) then y ⟨j.1.val,h⟩ else 0 else 0
  refine ⟨g,?_⟩
  ext r
  simp [bidiagonalObstructionMap,g,Fin.sum_univ_succ,r.isLt]

theorem bidiagonalObstructionMap_coefficient_zero (m d : ℕ)
    (v : Fin (m+1) × Fin (d+1) → K) :
    bidiagonalObstructionMap m d
      (polynomialCoefficientMatrix (bidiagonalPencil (K:=K) m) d *ᵥ v)=0 := by
  classical
  let z := coefficientVectorPolynomial d v
  let w : ℕ → K[X] := fun t => if h : t<m+1 then z ⟨t,h⟩ else 0
  ext r
  change (∑ s : Fin (d+2), (-1:K)^s.val*
    (polynomialCoefficientMatrix (bidiagonalPencil m) d *ᵥ v)
      (⟨r.val+s.val,by have := r.isLt; have := s.isLt; omega⟩,s))=0
  simp_rw [polynomialCoefficientMatrix_mulVec,bidiagonalPencil_mulVec]
  have he : (∑ s : Fin (d+2), (-1:K)^s.val*
      (X*w (r.val+s.val)+w (r.val+s.val+1)).coeff s.val)=0 := by
    let f : ℕ → K := fun s => (-1:K)^s*
      (X*w (r.val+s)+w (r.val+s+1)).coeff s
    change (∑ s : Fin (d+2), f s.val)=0
    rw [Fin.sum_univ_eq_sum_range f (d+2)]
    dsimp only [f]
    have ht := coefficient_telescope (fun t => w (r.val+t)) (d+1)
    simp only [Nat.add_assoc,Nat.reduceAdd] at ht ⊢
    rw [ht]
    have hlast : r.val+(d+2)<m+1 := by have := r.isLt; omega
    simp only [w,hlast,dif_pos]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (Nat.lt_succ_of_le (coefficientVectorPolynomial_degree d v _)),mul_zero]
  convert he using 1
  apply Finset.sum_congr rfl
  intro s _
  have h0 : r.val+s.val<m+1 := by have := r.isLt; have := s.isLt; omega
  have h1 : r.val+s.val+1<m+1 := by have := r.isLt; have := s.isLt; omega
  simp only [w,h0,h1,dif_pos]
  rfl

theorem bidiagonal_coefficient_range_eq_obstruction_kernel (m d : ℕ) :
    LinearMap.range (Matrix.toLin' (polynomialCoefficientMatrix (bidiagonalPencil (K:=K) m) d))=
      LinearMap.ker (bidiagonalObstructionMap (K:=K) m d) := by
  have hle : LinearMap.range
      (Matrix.toLin' (polynomialCoefficientMatrix (bidiagonalPencil (K:=K) m) d))≤
      LinearMap.ker (bidiagonalObstructionMap (K:=K) m d) := by
    rintro g ⟨v,rfl⟩
    exact bidiagonalObstructionMap_coefficient_zero m d v
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hB := (Matrix.toLin'
    (polynomialCoefficientMatrix (bidiagonalPencil (K:=K) m) d)).finrank_range_add_finrank_ker
  rw [coefficient_kernel_finrank _ _ (bidiagonalPencil_degree m),bidiagonal_kernel_hilbert] at hB
  have hO := (bidiagonalObstructionMap (K:=K) m d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (bidiagonalObstructionMap_surjective m d),finrank_top] at hO
  simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_prod,Fintype.card_fin] at hB hO
  by_cases h : m≤d+1
  · have h0 : m-(d+1)=0 := by omega
    have hsub := Nat.sub_add_cancel h
    nlinarith
  · have h0 : d+1-m=0 := by omega
    have hsub : m-(d+1)+(d+1)=m := by omega
    nlinarith

theorem bidiagonal_bounded_lift_iff (m d : ℕ) (g : Fin m → K[X])
    (hg : ∀ i, (g i).natDegree≤d+1) :
    (∃ v : Fin (m+1) → K[X], (∀ j, (v j).natDegree≤d) ∧
      bidiagonalPencil m *ᵥ v=g) ↔
    bidiagonalObstructionMap m d (fun ik => (g ik.1).coeff ik.2.val)=0 := by
  classical
  constructor
  · rintro ⟨v,hv,hBg⟩
    let c : Fin (m+1) × Fin (d+1) → K := fun jl => (v jl.1).coeff jl.2.val
    have hc : coefficientVectorPolynomial d c=v := by
      funext j
      exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
        (p:=v j) (n:=d+1) (by have := hv j; omega)
    have hcoeff : polynomialCoefficientMatrix (bidiagonalPencil m) d *ᵥ c=
        fun ik => (g ik.1).coeff ik.2.val := by
      ext ik
      rw [polynomialCoefficientMatrix_mulVec,hc,hBg]
    rw [← hcoeff]
    exact bidiagonalObstructionMap_coefficient_zero m d c
  · intro h
    have hmem : (fun ik : Fin m × Fin (d+2) => (g ik.1).coeff ik.2.val)∈
        LinearMap.ker (bidiagonalObstructionMap m d) := h
    rw [← bidiagonal_coefficient_range_eq_obstruction_kernel] at hmem
    obtain ⟨c,hc⟩ := hmem
    refine ⟨coefficientVectorPolynomial d c,coefficientVectorPolynomial_degree d c,?_⟩
    funext i
    apply Polynomial.ext
    intro k
    by_cases hk : k<d+2
    · have hh := congrFun hc (i,⟨k,hk⟩)
      rw [Matrix.toLin'_apply,polynomialCoefficientMatrix_mulVec] at hh
      exact hh
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
          (polynomial_mulVec_degree _ _ d (bidiagonalPencil_degree m)
            (coefficientVectorPolynomial_degree d c) i) (by omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hg i) (by omega))]

theorem bidiagonal_scalar_lift_iff (m d : ℕ) (a : Fin m → K)
    (c : K[X]) (hc : c.natDegree≤d+1) :
    (∃ v : Fin (m+1) → K[X], (∀ j, (v j).natDegree≤d) ∧
      bidiagonalPencil m *ᵥ v=fun i => c*C (a i)) ↔
    ∀ r : Fin (m-(d+1)),
      (∑ s : Fin (d+2), (-1:K)^s.val*a ⟨r.val+s.val,by
        have := r.isLt; have := s.isLt; omega⟩*c.coeff s.val)=0 := by
  rw [bidiagonal_bounded_lift_iff m d _ (fun i => (natDegree_mul_C_le _ _).trans hc)]
  simp only [bidiagonalObstructionMap,LinearMap.coe_mk,AddHom.coe_mk,
    funext_iff,Pi.zero_apply,Polynomial.coeff_mul_C]
  simp only [mul_assoc,mul_comm (c.coeff _) (a _)]

end FD56
