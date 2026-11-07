import FeasibleThresholdRemovalWitness
namespace JSP452Audit.StarHost
open SimpleGraph

noncomputable def componentSlots {X : Type*} [Finite X] (H : SimpleGraph X) (h : ℕ) : ℕ := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  exact ∑c:H.ConnectedComponent,Nat.card c.supp/(h+1)

/-- Threshold-h stars in one packing consume h+1 original slots in
one common component per star, with no vertex reused. -/
theorem removed_threshold_below_slots {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X)
    (n : Fin s→ℕ) (h : ℕ) (T : ↥(componentBudget H n).choices) :
    (T.val.filter (fun i => h≤n i)).card≤componentSlots H h := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  let E := T.val.filter (fun i => h≤n i)
  let orig (z:↥E) : ↥T.val := ⟨z.val,(Finset.mem_filter.mp z.property).1⟩
  let m (z:↥T.val) := n z.val
  obtain ⟨_,pack⟩ := (mem_component_budget H n T.val).mp T.property
  obtain ⟨f,assign⟩ := pack
  let slot (z:↥E) (j:Fin (h+1)) : Fin (m (orig z)+1) :=
    ⟨j.val,by have hi := (Finset.mem_filter.mp z.property).2;have jt := j.isLt;change _<n z.val+1;omega⟩
  let owner (z:↥E) := H.connectedComponentMk (f (center m (orig z)))
  let A (c:H.ConnectedComponent) := {z:↥E | owner z=c}
  have per (c:H.ConnectedComponent) : Nat.card ↥(A c)≤Nat.card c.supp/(h+1) := by
    let send (p:↥(A c) × Fin (h+1)) : c.supp :=
      ⟨f ⟨orig p.1.val,slot p.1.val p.2⟩,(assign _ _).symm.trans p.1.property⟩
    have inj : Function.Injective send := by
      intro p q eq
      have same := f.injective (congrArg (fun z:c.supp => z.val) eq)
      apply Prod.ext
      · apply Subtype.ext
        exact Subtype.ext (congrArg (fun z:Vertices m => z.1.val) same)
      · exact Fin.ext (congrArg (fun z:Vertices m => z.2.val) same)
    have bound := Nat.card_le_card_of_injective send inj
    rw [Nat.card_prod,Nat.card_fin] at bound
    exact (Nat.le_div_iff_mul_le (by omega : 0<h+1)).2 bound
  have budget := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => per c)
  have unpack := Nat.card_congr (Equiv.sigmaFiberEquiv owner)
  rw [Nat.card_sigma] at unpack
  change (∑c:H.ConnectedComponent,Nat.card ↥(A c))=Nat.card ↥E at unpack
  rw [unpack,Nat.card_eq_fintype_card,Fintype.card_coe] at budget
  exact budget

theorem actual_threshold_capacity {s : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X)
    (n : Fin s→ℕ) (hn : Antitone n) (h : ℕ) :
    originalThresholdCount n h≤originalThresholdCount ((componentBudget H n).entries n) h+componentSlots H h := by
  obtain ⟨T,required⟩ := threshold_removal_witness n hn (componentBudget H n) h
  exact required.trans (Nat.add_le_add_left (removed_threshold_below_slots H n h T) _)

#print axioms removed_threshold_below_slots
#print axioms actual_threshold_capacity
end JSP452Audit.StarHost
