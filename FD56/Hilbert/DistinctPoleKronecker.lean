/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DistinctPoleKernel
import FD56.Hilbert.SkewCrossKernel

/-! The trace-hyperplane diagonal pencil is one Kronecker block. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem poleTracePencil_degree (lam : n → K) (i₀ : n) : DegreeBound (poleTracePencil lam i₀) 1 := by
  intro j i
  rw [poleTracePencil_entry]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem poleTracePencil_transpose_kernel_zero (lam : n → K) (i₀ : n)
    (x : {j : n // j≠i₀} → K[X]) (hx : (poleTracePencil lam i₀).transpose *ᵥ x=0) : x=0 := by
  funext j
  have h := congrFun hx j.val
  rw [poleTracePencil_transpose_mulVec] at h
  exact (mul_eq_zero.mp h).resolve_left (Polynomial.X_sub_C_ne_zero _)

theorem poleTraceSkew_low_hilbert_zero (lam : n → K) (hlam : Function.Injective lam)
    (i₀ : n) (d : ℕ) (hd : d<Fintype.card n-1) :
    Module.finrank K (polynomialKernelAtDegree (skewCrossMatrix (poleTracePencil lam i₀)) d)=0 := by
  apply Submodule.finrank_eq_zero.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  let v : {j : n // j≠i₀} ⊕ n → K[X] := fun i => (z i).val
  have hv : skewCrossMatrix (poleTracePencil lam i₀) *ᵥ v=0 := hz
  obtain ⟨hy,hx⟩ := (skewCrossMatrix_kernel_iff _ _).mp hv
  have hy0 := poleTracePencil_low_degree_zero lam hlam i₀ (v ∘ Sum.inr) d hd
    (fun i => boundedPoly_degree d (z (.inr i))) hy
  have hx0 := poleTracePencil_transpose_kernel_zero lam i₀ (v ∘ Sum.inl) hx
  funext i
  apply Subtype.ext
  cases i with
  | inl i => exact congrFun hx0 i
  | inr i => exact congrFun hy0 i

theorem poleTraceSkew_minimal_degrees [Nontrivial n] (lam : n → K)
    (hlam : Function.Injective lam) (i₀ : n) :
    HasMinimalKernelDegrees (skewCrossMatrix (poleTracePencil lam i₀)) [Fintype.card n-1] := by
  let P := skewCrossMatrix (poleTracePencil lam i₀)
  let A := fun i j => (P i j).coeff 0
  let B := fun i j => (P i j).coeff 1
  have he : affineMatrixPencil A B=P := affineMatrixPencil_coefficients P
    (skewCrossMatrix_degreeBound _ _ (poleTracePencil_degree lam i₀))
  have hsk (k : ℕ) : (Matrix.of fun i j => (P i j).coeff k).transpose =
      -(Matrix.of fun i j => (P i j).coeff k) := by
    change (Matrix.of fun i j => (skewCrossMatrix (poleTracePencil lam i₀) i j).coeff k).transpose = _
    rw [skewCrossMatrix_coefficient]
    exact skewCrossMatrix_skew _
  obtain ⟨r,b,e,hZ,hL,_,_⟩ := polynomial_kernel_has_minimal_basis P
  have hm : HasMinimalKernelDegrees P (List.ofFn e) := ⟨r,b,e,hZ,hL,List.Perm.refl _⟩
  have hne : List.ofFn e≠[] := by
    intro hz
    have hh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hm (Fintype.card n-1)
    rw [hz] at hh
    simp only [List.map_nil,List.sum_nil] at hh
    let v : {j : n // j≠i₀} ⊕ n → K[X] := Sum.elim (fun _ => 0) (poleCofactor lam)
    have hv : P *ᵥ v=0 := (skewCrossMatrix_kernel_iff _ _).mpr ⟨by
      simpa only [v,Function.comp_def,Sum.elim_inr] using poleTracePencil_cofactor_kernel lam i₀,
      by change (poleTracePencil lam i₀).transpose *ᵥ (0 : {j : n // j≠i₀} → K[X])=0
         exact Matrix.mulVec_zero _⟩
    have hdv : ∀ i, (v i).natDegree ≤ Fintype.card n-1 := by
      intro i
      cases i with
      | inl i => simp [v]
      | inr i => exact (poleCofactor_degree lam i).le
    have hv0 := polynomial_kernel_vector_zero_of_hilbert_zero P _ hh v hv hdv
    exact poleCofactor_ne_zero lam i₀ (congrFun hv0 (.inr i₀))
  have hn : 2≤Fintype.card n := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hcard : Fintype.card ({j : n // j≠i₀} ⊕ n)=2*(Fintype.card n-2)+3 := by
    simp only [Fintype.card_sum,Fintype.card_subtype_compl,Fintype.card_subtype_eq]
    omega
  have hzero := poleTraceSkew_low_hilbert_zero lam hlam i₀ (Fintype.card n-2) (by omega)
  have hx := skew_pencil_single_degree_of_kernel_vanishing A B (Fintype.card n-2) (List.ofFn e)
    (he ▸ hm) hne hcard (hsk 0) (hsk 1) (he ▸ hzero)
  have hd : Fintype.card n-2+1=Fintype.card n-1 := by omega
  rw [hd] at hx
  rwa [hx] at hm

theorem poleTraceSkew_kronecker_decomposition [Nontrivial n] (lam : n → K)
    (hlam : Function.Injective lam) (i₀ : n) :
    HasKroneckerDecomposition (skewCrossMatrix (poleTracePencil lam i₀)) [Fintype.card n-1] := by
  let P := skewCrossMatrix (poleTracePencil lam i₀)
  let A := fun i j => (P i j).coeff 0
  let B := fun i j => (P i j).coeff 1
  have he : affineMatrixPencil A B=P := affineMatrixPencil_coefficients P
    (skewCrossMatrix_degreeBound _ _ (poleTracePencil_degree lam i₀))
  have hsk (k : ℕ) : (Matrix.of fun i j => (P i j).coeff k).transpose =
      -(Matrix.of fun i j => (P i j).coeff k) := by
    change (Matrix.of fun i j => (skewCrossMatrix (poleTracePencil lam i₀) i j).coeff k).transpose = _
    rw [skewCrossMatrix_coefficient]
    exact skewCrossMatrix_skew _
  have halt (k : ℕ) (v : {j : n // j≠i₀} ⊕ n → K) :
      v ⬝ᵥ ((Matrix.of fun i j => (P i j).coeff k) *ᵥ v)=0 := by
    change v ⬝ᵥ ((Matrix.of fun i j => (skewCrossMatrix (poleTracePencil lam i₀) i j).coeff k) *ᵥ v)=0
    rw [skewCrossMatrix_coefficient]
    exact skewCrossMatrix_alternating _ _
  have hn : 2≤Fintype.card n := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  have hcard : Fintype.card ({j : n // j≠i₀} ⊕ n)=
      ([Fintype.card n-1].map (fun e => 2*e+1)).sum := by
    simp only [Fintype.card_sum,Fintype.card_subtype_compl,Fintype.card_subtype_eq,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    omega
  obtain ⟨r,d,hp,T,S,hTS,hST,hcong⟩ := exists_mixed_kronecker_canonical A B [Fintype.card n-1]
    (he ▸ poleTraceSkew_minimal_degrees lam hlam i₀) hcard (hsk 0) (hsk 1) (halt 0) (halt 1)
  refine ⟨r,d,hp,T,S,hTS,hST,?_⟩
  simpa only [he] using hcong

end FD56
