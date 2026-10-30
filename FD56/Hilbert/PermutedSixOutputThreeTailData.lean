/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.NatDotCertificate

/-! Exact inverse data for a six-output degree-three tail. -/

namespace FD56
open Matrix
set_option Elab.async false

private def uRow0 : List ℤ := [0,0,0,1]
private def uRow1 : List ℤ := [0,0,0,0]
private def uRow2 : List ℤ := [1,0,0,0]
private def uRow3 : List ℤ := [0,0,0,0]
private def uRow4 : List ℤ := [0,0,1,0]
private def uRow5 : List ℤ := [0,1,0,0]
private def uRowTable : List (List ℤ) := [uRow0,uRow1,uRow2,uRow3,uRow4,uRow5]
def permutedSixOutputThreeTailUData (i : Fin 6) : List ℤ := uRowTable.getD i.val []

private def vRow0 : List ℤ := [0,0,0,0]
private def vRow1 : List ℤ := [0,0,1,-1]
private def vRow2 : List ℤ := [0,0,0,0]
private def vRow3 : List ℤ := [-1,1,0,0]
private def vRow4 : List ℤ := [0,0,1,0]
private def vRow5 : List ℤ := [0,1,0,0]
private def vRowTable : List (List ℤ) := [vRow0,vRow1,vRow2,vRow3,vRow4,vRow5]
def permutedSixOutputThreeTailVData (i : Fin 6) : List ℤ := vRowTable.getD i.val []

private def inverseRow0 : List ℕ := [100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow1 : List ℕ := [100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow2 : List ℕ := [2,1,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow3 : List ℕ := [99,100,100,100,100,0,0,100,100,100,100,100,100,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow4 : List ℕ := [100,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow5 : List ℕ := [97,98,99,99,100,0,0,100,100,100,100,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow6 : List ℕ := [100,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow7 : List ℕ := [99,100,0,0,0,0,0,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow8 : List ℕ := [100,100,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow9 : List ℕ := [1,0,0,0,0,0,0,1,1,1,0,0,0,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow10 : List ℕ := [3,2,1,1,1,0,0,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow11 : List ℕ := [100,100,100,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow12 : List ℕ := [2,1,2,2,1,0,0,0,0,1,1,1,1,1,0,0,0,0,100,100,0,0,0,2,1,0,0,1,1,1]
private def inverseRow13 : List ℕ := [98,100,99,99,100,0,0,0,0,100,100,100,100,100,0,0,0,0,2,2,1,1,1,99,100,0,0,100,100,100]
private def inverseRow14 : List ℕ := [0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow15 : List ℕ := [0,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0]
private def inverseRow16 : List ℕ := [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0]
private def inverseRow17 : List ℕ := [1,1,0,0,0,0,0,1,1,0,0,0,0,100,0,0,0,0,1,1,0,0,0,100,0,0,0,100,100,100]
private def inverseRow18 : List ℕ := [1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow19 : List ℕ := [1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow20 : List ℕ := [1,0,0,0,0,0,0,1,1,1,1,0,0,100,100,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow21 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow22 : List ℕ := [100,0,0,0,0,0,0,100,100,100,100,100,100,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow23 : List ℕ := [100,0,0,0,0,0,0,100,100,100,100,100,100,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0]
private def inverseRow24 : List ℕ := [1,2,0,0,0,0,0,1,1,0,0,0,0,100,0,0,0,0,2,2,1,0,0,99,100,0,0,100,100,100]
private def inverseRow25 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0]
private def inverseRow26 : List ℕ := [0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,100,100,100,100,1,1,1,0,0,0,0]
private def inverseRow27 : List ℕ := [0,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,100,100,100,100,1,1,1,1,0,0,0]
private def inverseRow28 : List ℕ := [0,100,0,0,0,0,0,0,0,1,0,0,0,0,100,0,0,0,100,100,0,0,0,1,0,0,0,1,0,0]
private def inverseRow29 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100]
private def inverseRowTable : List (List ℕ) := [inverseRow0,inverseRow1,inverseRow2,inverseRow3,inverseRow4,inverseRow5,inverseRow6,inverseRow7,inverseRow8,inverseRow9,inverseRow10,inverseRow11,inverseRow12,inverseRow13,inverseRow14,inverseRow15,inverseRow16,inverseRow17,inverseRow18,inverseRow19,inverseRow20,inverseRow21,inverseRow22,inverseRow23,inverseRow24,inverseRow25,inverseRow26,inverseRow27,inverseRow28,inverseRow29]
def permutedSixOutputThreeTailInverseRows (i : Fin 30) : List ℕ := inverseRowTable.getD i.val []

private def selectedColumn0 : List ℕ := [100,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,100,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn1 : List ℕ := [0,100,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1,100,0,0,0,100,0,0,0,0,0,0]
private def selectedColumn2 : List ℕ := [0,0,0,0,0,0,0,0,0,1,100,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn3 : List ℕ := [0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn4 : List ℕ := [0,0,100,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,1,100,0,0,0,0,0]
private def selectedColumn5 : List ℕ := [0,0,0,100,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,1,100,0,0,0,0]
private def selectedColumn6 : List ℕ := [0,0,0,0,0,0,0,100,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn7 : List ℕ := [0,0,0,0,0,0,0,0,100,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,0,0]
private def selectedColumn8 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,100,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0]
private def selectedColumn9 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,100,1,0,0,0,0,0,0,0,0,0,0,0,100,1,0]
private def selectedColumn10 : List ℕ := [0,0,0,100,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn11 : List ℕ := [0,0,0,0,100,1,0,0,0,0,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn12 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0]
private def selectedColumn13 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0]
private def selectedColumn14 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn15 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,1,0,0]
private def selectedColumn16 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,100,0,0]
private def selectedColumn17 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,100,0]
private def selectedColumn18 : List ℕ := [0,0,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn19 : List ℕ := [0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn20 : List ℕ := [0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn21 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn22 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn23 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0]
private def selectedColumn24 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,0,0]
private def selectedColumn25 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0,0,0,0,0]
private def selectedColumn26 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0,0,0]
private def selectedColumn27 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0]
private def selectedColumn28 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100,0]
private def selectedColumn29 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,100]
private def selectedColumnTable : List (List ℕ) := [selectedColumn0,selectedColumn1,selectedColumn2,selectedColumn3,selectedColumn4,selectedColumn5,selectedColumn6,selectedColumn7,selectedColumn8,selectedColumn9,selectedColumn10,selectedColumn11,selectedColumn12,selectedColumn13,selectedColumn14,selectedColumn15,selectedColumn16,selectedColumn17,selectedColumn18,selectedColumn19,selectedColumn20,selectedColumn21,selectedColumn22,selectedColumn23,selectedColumn24,selectedColumn25,selectedColumn26,selectedColumn27,selectedColumn28,selectedColumn29]
def permutedSixOutputThreeTailSelectedColumns (i : Fin 30) : List ℕ := selectedColumnTable.getD i.val []

def permutedSixOutputThreeTailSelectedRows : Fin 30 → Fin 120 := ![0,1,2,3,4,5,6,10,11,12,13,14,15,18,19,20,21,22,27,28,29,30,31,35,36,37,38,45,46,47]

def permutedSixOutputThreeTailSelectedData : Matrix (Fin 30) (Fin 30) ℕ :=
  fun i j => (permutedSixOutputThreeTailSelectedColumns j).getD i.val 0

def permutedSixOutputThreeTailSelected : Matrix (Fin 30) (Fin 30) (ZMod 101) :=
  fun i j => permutedSixOutputThreeTailSelectedData i j

end FD56
