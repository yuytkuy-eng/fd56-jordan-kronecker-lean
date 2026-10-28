/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FourOutputGradientRowModule
import FD56.Hilbert.FourOutputMinorPrimitive
import FD56.Hilbert.FourOutputInteriorSLTests
import FD56.Hilbert.ReducedFactorDualDegrees
import FD56.Hilbert.GenericTerminalDegreeBudget

/-! The actual generic SL minimal degrees and the minimal degrees of the
six-minor polar row are complementary. The exact row-module identity and
the two total-degree budgets establish this without a balance hypothesis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem factor_transpose_range_of_kernel
    {R a n r s : Type*} [CommRing R]
    [Fintype n] [Fintype r] [Fintype s]
    [DecidableEq n] [DecidableEq r] [DecidableEq s]
    (V : Matrix n r R) (C : Matrix r s R) (A : Matrix a s R)
    (hV : Function.Injective V.mulVec)
    (hgen : LinearMap.range (Matrix.toLin' (V*C).transpose)=
      LinearMap.ker (Matrix.toLin' A)) :
    LinearMap.range (Matrix.toLin' C.transpose)=LinearMap.ker (Matrix.toLin' A) := by
  have hAZ : A*(V*C).transpose=0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,map_zero]
    exact LinearMap.range_le_ker_iff.mp (le_of_eq hgen)
  have hVC : V*(C*A.transpose)=0 := by
    have h := congrArg Matrix.transpose hAZ
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,
      Matrix.transpose_zero,Matrix.mul_assoc] using h
  have hCA : C*A.transpose=0 :=
    matrix_left_mul_injective_of_mulVec V hV (hVC.trans (Matrix.mul_zero V).symm)
  have hAC : A*C.transpose=0 := by
    have h := congrArg Matrix.transpose hCA
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_zero] using h
  apply le_antisymm
  · apply LinearMap.range_le_ker_iff.mpr
    rw [← Matrix.toLin'_mul,hAC,map_zero]
  · intro x hx
    rw [← hgen] at hx
    obtain ⟨u,hu⟩ := hx
    refine ⟨V.transpose*ᵥu,?_⟩
    change C.transpose*ᵥ(V.transpose*ᵥu)=x
    rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul]
    exact hu

private theorem minimal_degree_lists_perm
    {K a n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix a n K[X]) (xs ys : List ℕ)
    (hx : HasMinimalKernelDegrees A xs) (hy : HasMinimalKernelDegrees A ys) :
    xs.Perm ys := by
  apply listHilbert_determines_indices
  intro d
  rw [listHilbert_nat,listHilbert_nat]
  exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert A xs).mp hx d).symm.trans
    ((hasMinimalKernelDegrees_iff_hilbert A ys).mp hy d)

private theorem complementary_degrees_bound {r : ℕ} (e : Fin r → ℕ) (D : ℕ)
    (hbudget : (∑ i : Fin r, (D-e i))+(∑ i : Fin r, e i)=r*D) :
    ∀ i : Fin r, e i≤D := by
  have hsum : (∑ _i : Fin r, D)=∑ i : Fin r, ((D-e i)+e i) := by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul] using hbudget.symm
  have hall := (Finset.sum_eq_sum_iff_of_le
    (fun (i : Fin r) (_ : i∈Finset.univ) => show D≤(D-e i)+e i by omega)).mp hsum
  intro i
  have hi := hall i (Finset.mem_univ i)
  omega

variable {K : Type*} [Field K]

theorem generic_four_output_sl_dual_degrees_of_bases (q : ℕ) (hq : 0<q)
    (i₀ : Fin (4*q+2))
    (Bv : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) q))))
    (Bt : Basis (Fin 2)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin'
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)*
          (genericAffineSquare K (Fin (4*q+2)) (Fin 4))^q*
          polynomialKernelBasisMatrix _ Bv).transpose)))
    (Bsl : Basis (Fin 5)
      (AffineCoefficientField K (MatrixParameters (Fin (4*q+2)) (Fin 4)))[X]
      (LinearMap.ker (Matrix.toLin' (slEquationMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀))))
    (e : Fin 5 → ℕ)
    (he : ∀ i j, (polynomialKernelBasisMatrix _ Bsl i j).natDegree≤e j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ Bsl i j).coeff (e j)))) :
    (∀ i, e i≤2*(q+1)^2-1) ∧
      HasMinimalKernelDegrees
        (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q))
        (List.ofFn (fun i => (2*(q+1)^2-1)-e i)) := by
  classical
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let S := slEquationMatrix M P i₀
  let U := polynomialKernelBasisMatrix S Bsl
  let Z := fourOutputScalarLiftMatrix q M P
  let A := pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q)
  obtain ⟨C,hUC⟩ := polynomialKernelFrame_factor S Bsl Z
    (fourOutputScalarLiftMatrix_kernel q M P i₀)
  have hgen : LinearMap.range (Matrix.toLin' C.transpose)=LinearMap.ker (Matrix.toLin' A) := by
    apply factor_transpose_range_of_kernel U C A
      (polynomialKernelBasisMatrix_injective S Bsl)
    rw [hUC]
    exact generic_four_output_gradient_row_range q Bv Bt
  have hminSL : HasMinimalKernelDegrees S (List.ofFn e) :=
    ⟨5,Bsl,e,he,hlead,List.Perm.refl _⟩
  obtain ⟨ys,_,hySum,hyMin,_⟩ :=
    generic_four_output_interior_sl_degree_budget (K:=K) q hq i₀
  have heSum : (∑ i, e i)=8*q^2+16*q+3 := by
    have h := (minimal_degree_lists_perm S (List.ofFn e) ys hminSL hyMin).sum_eq
    simpa only [List.sum_ofFn,hySum] using h
  obtain ⟨k,Bf,f,hf,hfl,_,_⟩ := polynomial_kernel_has_minimal_basis A
  have hfMin : HasMinimalKernelDegrees A (List.ofFn f) :=
    ⟨k,Bf,f,hf,hfl,List.Perm.refl _⟩
  obtain ⟨hfLen,hfSum⟩ := generic_four_output_polar_minimal_degree_budget q Bv _ hfMin
  have hbudget : (List.ofFn f).sum+(∑ i, e i)=5*(2*(q+1)^2-1) := by
    rw [hfSum,heSum]
    have hW : 1≤2*(q+1)^2 := by nlinarith
    have hsub := Nat.sub_add_cancel hW
    nlinarith
  have hdual := reduced_factor_dual_minimal_degrees U C e (2*(q+1)^2-1)
    he hlead (by rw [hUC]; exact generic_four_output_scalar_lift_degree (K:=K) q)
    A hgen (List.ofFn f) hfMin hfLen hbudget
  have hdualSum := (generic_four_output_polar_minimal_degree_budget q Bv _ hdual).2
  simp only [List.sum_ofFn] at hdualSum
  refine ⟨complementary_degrees_bound e (2*(q+1)^2-1) ?_,hdual⟩
  rw [hdualSum]
  simpa only [hfSum] using hbudget

theorem generic_four_output_sl_dual_degrees (q : ℕ) (hq : 0<q) (i₀ : Fin (4*q+2)) :
    ∃ e : Fin 5 → ℕ,
      (∀ i, e i≤2*(q+1)^2-1) ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K (Fin (4*q+2)) (Fin 4))
        (genericAffineRows K (Fin (4*q+2)) (Fin 4)) i₀) (List.ofFn e) ∧
      HasMinimalKernelDegrees
        (pluckerPolarRow (genericFourOutputInteriorMinors (K:=K) q))
        (List.ofFn (fun i => (2*(q+1)^2-1)-e i)) := by
  let M := genericAffineSquare K (Fin (4*q+2)) (Fin 4)
  let P := genericAffineRows K (Fin (4*q+2)) (Fin 4)
  let O := observabilityMatrix M P q
  have hlo : q*Fintype.card (Fin 4)<Fintype.card (Fin (4*q+2)) := by
    simp only [Fintype.card_fin]; omega
  have hhi : Fintype.card (Fin (4*q+2))<(q+1)*Fintype.card (Fin 4) := by
    simp only [Fintype.card_fin]; omega
  obtain ⟨r,Bv,a,hv,hvl,_,_⟩ := polynomial_kernel_has_minimal_basis O
  have haMin : HasMinimalKernelDegrees O (List.ofFn a) :=
    ⟨r,Bv,a,hv,hvl,List.Perm.refl _⟩
  have hr := (generic_observability_kernel_degree_budget (K:=K) q hlo _ haMin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hr
  have hr2 : r=2 := by omega
  subst r
  let G := P*M^q*polynomialKernelBasisMatrix O Bv
  obtain ⟨s,Bt,b,ht,htl,_,_⟩ := polynomial_kernel_has_minimal_basis G.transpose
  have hbMin : HasMinimalKernelDegrees G.transpose (List.ofFn b) :=
    ⟨s,Bt,b,ht,htl,List.Perm.refl _⟩
  have hs := (generic_terminal_kernel_degree_budget (K:=K) q (by simp) hlo hhi
    Bv a hv hvl _ hbMin).1
  simp only [List.length_ofFn,Fintype.card_fin] at hs
  have hs2 : s=2 := by omega
  subst s
  obtain ⟨xs,hxs,_,hmin,_⟩ := generic_four_output_interior_sl_degree_budget (K:=K) q hq i₀
  obtain ⟨k,Bsl,e,he,hlead,hperm⟩ := hmin
  have hk : k=5 := by simpa only [List.length_ofFn,hxs] using hperm.length_eq
  subst k
  obtain ⟨hbound,hdual⟩ :=
    generic_four_output_sl_dual_degrees_of_bases q hq i₀ Bv Bt Bsl e he hlead
  exact ⟨e,hbound,⟨5,Bsl,e,he,hlead,List.Perm.refl _⟩,hdual⟩

end FD56
