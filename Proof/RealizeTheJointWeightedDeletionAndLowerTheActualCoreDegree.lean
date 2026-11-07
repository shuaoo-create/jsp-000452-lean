import SelectOneSetWithTheRequiredJointVertexAndSurvivingEdgeCost
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem weighted_actual_core_deletion {V:Type u} [Finite V] (C:SimpleGraph V) (D Z:ℕ)
    (degree:11≤D) (cap:∀v,Nat.card (C.neighborSet v)≤D) (order:D*Nat.card V≤(2*D+2)*Z) :
    ∃(A:Set V) (B:Set ↥(Aᶜ:Set V)),
      let C₁ := C.induce Aᶜ
      let C₂ := C₁.induce Bᶜ
      let k := A.ncard+B.ncard
      (∀v,Nat.card (C₂.neighborSet v)≤D-1) ∧
      3*(D-1)*k+2*C₂.edgeSet.ncard≤3*(D-1)*Z := by
  classical
  obtain ⟨f,budget⟩ := choose_one_weighted_fifth C D Z degree cap order
  let A := fifthChosen f
  let C₁ := C.induce Aᶜ
  have cap₁ (v:↥(Aᶜ:Set V)) : Nat.card (C₁.neighborSet v)≤D := (induced_neighbor_count_le C _ v).trans (cap v.val)
  obtain ⟨B,stage⟩ := complete_degree_stage_exists C₁ D
  let C₂ := C₁.induce Bᶜ
  have spent := JSP452Audit.StarHost.degree_on_independent_full_set C₁ B D stage.2.1 stage.1
  change C₁.edgeSet.ncard=C₂.edgeSet.ncard+D*B.ncard at spent
  have below := complete_stage_lowers_cap C₁ D B cap₁ stage
  have sub : Subtype.val '' B⊆fifthUndominated C D f := by
    rintro z ⟨v,mem,rfl⟩
    have real := stage.2.1 v mem
    have orig := (induced_neighbor_count_le C Aᶜ v)
    change Nat.card (C₁.neighborSet v)≤Nat.card (C.neighborSet v.val) at orig
    change Nat.card (C.neighborSet v.val)=D ∧ _
    refine ⟨le_antisymm (cap v.val) (real ▸ orig),?_⟩
    intro x hx
    rcases hx with eq|adj
    · exact eq ▸ v.property
    · exact all_neighbors_survive_of_induced_full C Aᶜ v D (cap v.val) real x adj
  have size := Set.ncard_le_ncard sub
  rw [Set.ncard_image_of_injective _ Subtype.val_injective] at size
  change 3*(D-1)*A.ncard+(D-3)*(fifthUndominated C D f).ncard+2*C₁.edgeSet.ncard≤3*(D-1)*Z at budget
  have shift := Nat.mul_le_mul_left (D-3) size
  have algebra : 3*(D-1)*B.ncard=(D-3)*B.ncard+2*(D*B.ncard) := by
    rw [←Nat.mul_assoc,show 3*(D-1)=(D-3)+2*D by omega,Nat.add_mul,Nat.mul_assoc]
  refine ⟨A,B,fun v => Nat.le_pred_of_lt (below v),?_⟩
  change 3*(D-1)*(A.ncard+B.ncard)+2*C₂.edgeSet.ncard≤3*(D-1)*Z
  rw [Nat.mul_add,algebra];omega

#print axioms weighted_actual_core_deletion
end JSP452Audit.StarHost