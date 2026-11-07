import FiniteSuppressionSingleExterior
import OriginalHighDegreeDoubleEscape
namespace JSP452Audit.StarHost

theorem single_strict_layer_sum (D b M K V j : ℕ) (C U f : ℕ→ℕ) (bpos : 2≤b) (hi : b<D)
    (jlo : 3≤j) (jhi : j≤b+1) (low : C 2≤M+U 2)
    (inside : ∀i,3≤ i → i≤b+1 → C i≤M+U i+f i)
    (strictMix : C j+V≤M+U j) (upper : ∀i,b+2≤ i → i≤D → C i+K≤M+U i+f i) :
    (∑z∈Finset.range (D-1),C (z+2))+(D-b-1)*K+V≤
      (D-1)*M+(∑z∈Finset.range (D-1),U (z+2))+(∑z∈Finset.range (D-2),f (z+3)) := by
  classical
  let E (i:ℕ) := if b+1< i then K else 0
  let S (i:ℕ) := if i=j then V else 0
  have point (z:ℕ) (hz:z∈Finset.range (D-2)) :
      C (z+3)+E (z+3)+S (z+3)≤M+U (z+3)+f (z+3) := by
    have span := Finset.mem_range.mp hz
    by_cases chosen : z+3=j
    · simp only [chosen,S,if_pos rfl,E,if_neg (by omega : ¬b+1<j),Nat.add_zero];omega
    by_cases above : b+1<z+3
    · simpa [E,S,above,chosen] using upper (z+3) (by omega) (by omega)
    · simpa [E,S,above,chosen] using inside (z+3) (by omega) (by omega)
  have all := Finset.sum_le_sum point
  simp only [Finset.sum_add_distrib] at all
  have num : (∑z∈Finset.range (D-2),E (z+3))=(D-b-1)*K := by
    rw [divide_at_opposing_head D b bpos hi E]
    have l : (∑z∈Finset.range (b-2),E (z+3))=0 := Finset.sum_eq_zero (by
      intro z hz;have := Finset.mem_range.mp hz;simp [E,show ¬b+1<z+3 by omega])
    rw [l]
    simp [E,show ∀z:ℕ,b+1<b+2+z by omega]
  have one : (∑z∈Finset.range (D-2),S (z+3))=V := by
    have at' := Finset.sum_eq_single (s:=Finset.range (D-2)) (f:=fun z => S (z+3)) (j-3)
      (fun z _ ne => by simp [S,show z+3≠j by omega]) (fun no => by have mem : j-3∈Finset.range (D-2) := Finset.mem_range.mpr (by omega);exact False.elim (no mem))
    simpa [S,show j-3+3=j by omega] using at'
  rw [num,one] at all
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at all
  have peel (F:ℕ→ℕ) : (∑z∈Finset.range (D-1),F (z+2))=F 2+(∑z∈Finset.range (D-2),F (z+3)) := by
    rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ'];simp [Nat.add_comm]
  have prod : (D-1)*M=(D-2)*M+M := by rw [show D-1=(D-2)+1 by omega,Nat.add_mul,Nat.one_mul]
  rw [peel C,peel U,prod]
  simp at all
  omega

#print axioms single_strict_layer_sum
end JSP452Audit.StarHost