import ActualTwoInventoryLedger
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The coordinate fee after repairing all high matching rows. -/
noncomputable def axisAllowance {s t D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r h : ℕ) : ℕ := by
  classical
  exact if 3≤h ∧ WinsHeight n m r h h 1 then doubleEnvelopeLoss G K n m r h else 0

theorem axis_allowance_sum {s t D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) (deg : 2≤D) :
    (∑q∈Finset.range (D-1),axisAllowance G K n m r (q+2))=
    ∑q∈matchingAxesFromThree n m r D,doubleEnvelopeLoss G K n m r (q+3) := by
  classical
  rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ']
  have zero : axisAllowance G K n m r 2=0 := by simp [axisAllowance]
  simp only [Nat.zero_add,zero,Nat.add_zero]
  rw [matchingAxesFromThree,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  rw [show q+1+2=q+3 by omega];simp [axisAllowance]

/-- The top layer pays both the original matching deficit and the
entire bound on the other matching-axis losses. -/
theorem fold_top_layer_payment (D d X : ℕ) (L C A : ℕ→ℕ) (deg : 2≤D)
    (top : 2*L D+2*X+2*d≤C D)
    (lower : ∀j,2≤j → j<D → 2*L j≤C j+A j)
    (all : (∑q∈Finset.range (D-1),A (q+2))≤2*X) :
    2*(∑q∈Finset.range (D-1),L (q+2))+2*d≤∑q∈Finset.range (D-1),C (q+2) := by
  have each (q:ℕ) (mem:q∈Finset.range (D-2)) := lower (q+2) (by omega) (by have := Finset.mem_range.mp mem;omega)
  have sums := Finset.sum_le_sum (s:=Finset.range (D-2)) each
  rw [←Finset.mul_sum,Finset.sum_add_distrib] at sums
  rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ,show D-2+2=D by omega] at all
  rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,show D-2+2=D by omega]
  omega

/-- Combined symbolic capacity, with both inventories taken on original
graphs with their labels preserved. -/
noncomputable def jointLayerCapacity {D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (h : ℕ) : ℕ :=
  K.roots.ncard+2*matchingEdges (G.induce K.core)+uniformEnvelope (G.induce K.rest) h+
    uniformEnvelope (eraseInternal G K.core) h

theorem joint_layer_capacity_sum {D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) :
    (∑q∈Finset.range (D-1),jointLayerCapacity G K (q+2))=
      (D-1)*(K.roots.ncard+2*matchingEdges (G.induce K.core))+
        interiorInventory (G.induce K.rest) D+interiorInventory (eraseInternal G K.core) D := by
  let M := K.roots.ncard+2*matchingEdges (G.induce K.core)
  change (∑q∈Finset.range (D-1),(M+uniformEnvelope (G.induce K.rest) (q+2)+
    uniformEnvelope (eraseInternal G K.core) (q+2)))=(D-1)*M+_+_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [interiorInventory]

#print axioms axis_allowance_sum
#print axioms fold_top_layer_payment
#print axioms joint_layer_capacity_sum
end JSP452Audit.StarHost
