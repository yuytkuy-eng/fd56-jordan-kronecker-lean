/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerLinearizedRelations

/-! A closed set of twenty original G(3,6) Plucker equations and its actual
linearization in the twenty increasing triple coordinates. -/

namespace FD56
open Matrix
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 6000000

def sixOutputTriple : Fin 20 → Fin 3 → Fin 6 := ![![0,1,2],![0,1,3],![0,1,4],![0,1,5],![0,2,3],![0,2,4],![0,2,5],![0,3,4],![0,3,5],![0,4,5],![1,2,3],![1,2,4],![1,2,5],![1,3,4],![1,3,5],![1,4,5],![2,3,4],![2,3,5],![2,4,5],![3,4,5]]

def sixOutputTripleRelationI : Fin 20 → Fin 2 → Fin 6 :=
  ![![0,1],![0,1],![0,1],![0,1],![0,1],![0,1],![0,1],![0,2],![0,2],![0,2],![3,4],![3,4],![3,4],![3,4],![3,4],![3,4],![3,4],![3,5],![3,5],![3,5]]

def sixOutputTripleRelationJ : Fin 20 → Fin 4 → Fin 6 :=
  ![![0,2,3,4],![0,2,3,5],![0,2,4,5],![1,2,3,4],![1,2,3,5],![1,2,4,5],![2,3,4,5],![1,2,3,4],![1,2,3,5],![1,2,4,5],![0,1,2,5],![0,1,3,5],![0,1,4,5],![0,2,3,5],![0,2,4,5],![1,2,3,5],![1,2,4,5],![0,1,4,5],![0,2,4,5],![1,2,4,5]]

def sixOutputOrderedTripleTerms (t : Fin 3 → Fin 6) : List (ℤ × Fin 20) :=
  (List.finRange 20).flatMap fun c =>
    let a := sixOutputTriple c 0
    let b := sixOutputTriple c 1
    let d := sixOutputTriple c 2
    if t 0=a ∧ t 1=b ∧ t 2=d then [(1,c)] else
    if t 0=b ∧ t 1=d ∧ t 2=a then [(1,c)] else
    if t 0=d ∧ t 1=a ∧ t 2=b then [(1,c)] else
    if t 0=d ∧ t 1=b ∧ t 2=a then [(-1,c)] else
    if t 0=b ∧ t 1=a ∧ t 2=d then [(-1,c)] else
    if t 0=a ∧ t 1=d ∧ t 2=b then [(-1,c)] else []

def sixOutputTripleRelationLeft (r : Fin 20) (k : Fin 4) : Fin 3 → Fin 6 :=
  ![sixOutputTripleRelationI r 0,sixOutputTripleRelationI r 1,sixOutputTripleRelationJ r k]

def sixOutputTripleRelationRight (r : Fin 20) (k : Fin 4) : Fin 3 → Fin 6 :=
  let j := sixOutputTripleRelationJ r
  (![![j 1,j 2,j 3],![j 0,j 2,j 3],![j 0,j 1,j 3],![j 0,j 1,j 2]] : Fin 4 → Fin 3 → Fin 6) k

def sixOutputTriplePluckerTerms (r : Fin 20) : List (ℤ × (Fin 20 × Fin 20)) :=
  (List.finRange 4).flatMap fun k =>
    (sixOutputOrderedTripleTerms (sixOutputTripleRelationLeft r k)).flatMap fun a =>
      (sixOutputOrderedTripleTerms (sixOutputTripleRelationRight r k)).map fun b =>
        ((if k.val%2=0 then 1 else -1)*a.1*b.1,(a.2,b.2))

def sixOutputTriplePluckerTermData : Fin 20 → List (ℤ × (Fin 20 × Fin 20)) :=
  ![[(-1,(0,7)),(1,(1,5)),(-1,(2,4))],
    [(-1,(0,8)),(1,(1,6)),(-1,(3,4))],
    [(-1,(0,9)),(1,(2,6)),(-1,(3,5))],
    [(-1,(0,13)),(1,(1,11)),(-1,(2,10))],
    [(-1,(0,14)),(1,(1,12)),(-1,(3,10))],
    [(-1,(0,15)),(1,(2,12)),(-1,(3,11))],
    [(1,(0,19)),(-1,(1,18)),(1,(2,17)),(-1,(3,16))],
    [(-1,(0,16)),(1,(4,11)),(-1,(5,10))],
    [(-1,(0,17)),(1,(4,12)),(-1,(6,10))],
    [(-1,(0,18)),(1,(5,12)),(-1,(6,11))],
    [(1,(7,12)),(-1,(13,6)),(1,(16,3)),(-1,(19,0))],
    [(1,(7,14)),(-1,(13,8)),(-1,(19,1))],
    [(1,(7,15)),(-1,(13,9)),(-1,(19,2))],
    [(1,(7,17)),(-1,(16,8)),(-1,(19,4))],
    [(1,(7,18)),(-1,(16,9)),(-1,(19,5))],
    [(1,(13,17)),(-1,(16,14)),(-1,(19,10))],
    [(1,(13,18)),(-1,(16,15)),(-1,(19,11))],
    [(1,(8,15)),(-1,(14,9)),(-1,(19,3))],
    [(1,(8,18)),(-1,(17,9)),(-1,(19,6))],
    [(1,(14,18)),(-1,(17,15)),(-1,(19,12))]]

theorem sixOutputTriplePluckerTerms_eq_data (r : Fin 20) :
    sixOutputTriplePluckerTerms r=sixOutputTriplePluckerTermData r := by
  revert r
  decide +kernel

variable {R : Type*} [CommRing R]

def sixOutputTriplePluckerMinors (G : Matrix (Fin 6) (Fin 3) R) : Fin 20 → R :=
  fun c => (G.submatrix (sixOutputTriple c) id).det

def sixOutputTriplePluckerQuadratic (p : Fin 20 → R) (r : Fin 20) : R :=
  ((sixOutputTriplePluckerTerms r).map fun t => (t.1 : R)*p t.2.1*p t.2.2).sum

def sixOutputTriplePluckerLinearized (p h : Fin 20 → R) (r : Fin 20) : R :=
  ((sixOutputTriplePluckerTerms r).map fun t =>
    (t.1 : R)*(h t.2.1*p t.2.2+p t.2.1*h t.2.2)).sum

def sixOutputTriplePluckerTangent (p : Fin 20 → R) : Matrix (Fin 20) (Fin 20) R :=
  fun r j => ((sixOutputTriplePluckerTerms r).map fun t =>
    (t.1 : R)*((if j=t.2.1 then p t.2.2 else 0)+(if j=t.2.2 then p t.2.1 else 0))).sum

theorem sixOutputTriplePluckerTangent_mulVec (p h : Fin 20 → R) (r : Fin 20) :
    (sixOutputTriplePluckerTangent p *ᵥ h) r=sixOutputTriplePluckerLinearized p h r := by
  have hlist (l : List (ℤ × (Fin 20 × Fin 20))) :
      (∑ j : Fin 20, (l.map (fun t => (t.1 : R)*
        ((if j=t.2.1 then p t.2.2 else 0)+(if j=t.2.2 then p t.2.1 else 0)))).sum*h j)=
      (l.map (fun t => (t.1 : R)*(h t.2.1*p t.2.2+p t.2.1*h t.2.2))).sum := by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib,ih]
      congr 1
      simp [mul_add,add_mul,Finset.sum_add_distrib,mul_ite,ite_mul]
      ring
  exact hlist (sixOutputTriplePluckerTerms r)

theorem sixOutputTriplePluckerQuadratic_linearization
    (p h : Fin 20 → R) (t : R) (r : Fin 20) :
    sixOutputTriplePluckerQuadratic (fun j => p j+t*h j) r=
      sixOutputTriplePluckerQuadratic p r+t*(sixOutputTriplePluckerTangent p *ᵥ h) r+
        t^2*sixOutputTriplePluckerQuadratic h r := by
  rw [sixOutputTriplePluckerTangent_mulVec]
  have hlist (l : List (ℤ × (Fin 20 × Fin 20))) :
      (l.map (fun c => (c.1 : R)*(p c.2.1+t*h c.2.1)*(p c.2.2+t*h c.2.2))).sum=
      (l.map (fun c => (c.1 : R)*p c.2.1*p c.2.2)).sum+
        t*(l.map (fun c => (c.1 : R)*(h c.2.1*p c.2.2+p c.2.1*h c.2.2))).sum+
        t^2*(l.map (fun c => (c.1 : R)*h c.2.1*h c.2.2)).sum := by
    induction l with
    | nil => simp
    | cons c l ih =>
      simp only [List.map_cons,List.sum_cons,ih]
      ring
  exact hlist (sixOutputTriplePluckerTerms r)

end FD56
