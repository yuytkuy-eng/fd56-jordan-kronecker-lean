/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialFunctionalAvoidance

/-! Split polynomial matrices over an extension field have primitive constant
row projections defined over the infinite base field, with finite avoidance. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L m : Type*} [Field K] [Field L] [Algebra K L] [Fintype m]

private def extensionProjectionEntry (G : Matrix m (Fin 2) L[X]) (j : Fin 2) :
    (m → K) →ₗ[K] L[X] where
  toFun u := ∑ i, u i • G i j
  map_add' u v := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c u := by simp [smul_smul,Finset.smul_sum]

private theorem extensionProjectionEntry_single [DecidableEq m]
    (G : Matrix m (Fin 2) L[X]) (i : m) (j : Fin 2) :
    extensionProjectionEntry (K:=K) G j (Pi.single i 1)=G i j := by
  classical
  simp [extensionProjectionEntry,Pi.single_apply]

omit [Fintype m] in
private theorem extension_line_submodule_parameters_finite
    (S : Submodule K (m → K)) (u v : m → K) (hv : v∉S) :
    {t : K | u+t•v∈S}.Finite := by
  apply Set.Subsingleton.finite
  intro t ht w hw
  by_contra htw
  have hdiff : (t-w)•v∈S := by
    convert S.sub_mem ht hw using 1
    simp [sub_smul]
  apply hv
  have hscaled := S.smul_mem ((t-w)⁻¹) hdiff
  simpa only [smul_smul,inv_mul_cancel₀ (sub_ne_zero.mpr htw),one_smul] using hscaled

theorem exists_coprime_constant_row_projection_extension_avoiding [Infinite K]
    (G : Matrix m (Fin 2) L[X]) (R : Matrix (Fin 2) m L[X]) (hRG : R*G=1)
    (s : Finset (Submodule K (m → K))) (hs : ∀ S∈s, S≠⊤) :
    ∃ u : m → K,
      IsCoprime (∑ i, C (algebraMap K L (u i))*G i 0)
        (∑ i, C (algebraMap K L (u i))*G i 1) ∧ ∀ S∈s, u∉S := by
  classical
  obtain ⟨i₀,hi₀⟩ : ∃ i : m, G i 0≠0 := by
    by_contra! hz
    have h := congrFun (congrFun hRG 0) 0
    simp [Matrix.mul_apply,hz] at h
  let f₀ := G i₀ 0
  let f₁ := G i₀ 1
  let wedge : (m → K) →ₗ[K] L[X] :=
    (LinearMap.mulLeft K f₀).comp (extensionProjectionEntry G 1)-
      (LinearMap.mulLeft K f₁).comp (extensionProjectionEntry G 0)
  have hwedge : LinearMap.ker wedge≠⊤ := by
    intro he
    have hz (i : m) : f₀*G i 1-f₁*G i 0=0 := by
      have hmem : Pi.single i (1:K)∈LinearMap.ker wedge := by rw [he]; trivial
      change f₀*extensionProjectionEntry G 1 (Pi.single i 1)-
        f₁*extensionProjectionEntry G 0 (Pi.single i 1)=0 at hmem
      simpa only [extensionProjectionEntry_single] using hmem
    apply hi₀
    change f₀=0
    calc
      f₀=f₀*(R*G) 1 1-f₁*(R*G) 1 0 := by simp [hRG]
      _=∑ i, R 1 i*(f₀*G i 1-f₁*G i 0) := by
        simp only [Matrix.mul_apply,Finset.mul_sum,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=0 := by simp [hz]
  have hunit : ∑ i, G i 0*R 0 i=1 := by
    simpa only [Matrix.mul_apply,Matrix.one_apply_eq,mul_comm] using
      congrFun (congrFun hRG 0) 0
  obtain ⟨v,hfg,hv⟩ := exists_coprime_constant_polynomial_functional_avoiding
    (fun i => G i 0) (fun i => R 0 i) hunit f₀ hi₀
    (insert (LinearMap.ker wedge) s) (by
      intro S hS
      rcases Finset.mem_insert.mp hS with rfl | hS
      · exact hwedge
      · exact hs S hS)
  let g₀ := extensionProjectionEntry G 0 v
  let g₁ := extensionProjectionEntry G 1 v
  have hfg' : IsCoprime f₀ g₀ := by
    simpa only [g₀,extensionProjectionEntry,LinearMap.coe_mk,AddHom.coe_mk,
      Algebra.smul_def,Polynomial.algebraMap_apply] using hfg
  have hdet : f₀*g₁-f₁*g₀≠0 :=
    hv (LinearMap.ker wedge) (Finset.mem_insert_self _ _)
  have hcopfiniteL : {t : L | ¬IsCoprime (f₀+C t*g₀) (f₁+C t*g₁)}.Finite :=
    finite_non_coprime_constant_row_combinations f₀ f₁ g₀ g₁ hdet
      (fun d hd₀ _ hd₁ _ => hfg'.isUnit_of_dvd' hd₀ hd₁)
  have hcopfinite : {t : K | ¬IsCoprime
      (f₀+C (algebraMap K L t)*g₀) (f₁+C (algebraMap K L t)*g₁)}.Finite :=
    hcopfiniteL.preimage (algebraMap K L).injective.injOn
  have hsubfinite : (⋃ S∈(s : Set (Submodule K (m → K))),
      {t : K | Pi.single i₀ 1+t•v∈S}).Finite := by
    apply s.finite_toSet.biUnion
    intro S hS
    exact extension_line_submodule_parameters_finite S (Pi.single i₀ 1) v
      (hv S (Finset.mem_insert_of_mem hS))
  obtain ⟨t,ht⟩ := (hcopfinite.union hsubfinite).exists_not_mem
  refine ⟨Pi.single i₀ 1+t•v,?_,?_⟩
  · have hcop : IsCoprime (f₀+C (algebraMap K L t)*g₀)
        (f₁+C (algebraMap K L t)*g₁) := not_not.mp (fun hn => ht (Or.inl hn))
    have hresult : IsCoprime
        (extensionProjectionEntry G 0 (Pi.single i₀ 1+t•v))
        (extensionProjectionEntry G 1 (Pi.single i₀ 1+t•v)) := by
      simp only [map_add,map_smul,extensionProjectionEntry_single]
      simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using hcop
    simpa only [extensionProjectionEntry,LinearMap.coe_mk,AddHom.coe_mk,
      Algebra.smul_def,Polynomial.algebraMap_apply] using hresult
  · intro S hS hmem
    exact ht (Or.inr (Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨hS,hmem⟩⟩))

end FD56
