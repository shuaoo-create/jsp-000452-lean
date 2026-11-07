import IndependentDominationOnThreeEdges
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

theorem short_stage_odd_six_regular {X:Type*} [Finite X] (Q:SimpleGraph X) (P:ℕ)
    (reg:∀x,Nat.card (Q.neighborSet x)=6) (order:Nat.card X=2*P+1) (edgeCount:Q.edgeSet.ncard=6*P+3) :
    ∃A:Set X,CompleteDegreeStage Q 6 A ∧ A.ncard+1≤P := by
  classical
  obtain ⟨I,ind,greatest⟩ := exists_largest_independent_set Q
  have split := Set.ncard_add_ncard_compl I
  have half := regular_independent_half Q I ind 6 (by decide) reg
  by_cases small : I.ncard+1≤P
  · refine ⟨I,⟨ind,fun x _ => reg x,?_⟩,small⟩
    intro v _
    by_cases mem:v∈I
    · exact Or.inl mem
    · exact Or.inr (largest_independent_dominates Q I ind greatest v mem)
  have exactI : I.ncard=P := by omega
  have rest : Iᶜ.ncard=P+1 := by omega
  let H := Q.induce Iᶜ
  have cost := JSP452Audit.StarHost.degree_on_independent_full_set Q I 6 (fun x _ => reg x) ind
  have three : H.edgeSet.ncard=3 := by change Q.edgeSet.ncard=H.edgeSet.ncard+6*I.ncard at cost;omega
  obtain ⟨J,stand,controls,low,hi⟩ := three_edge_independent_complement H three
  let A := Subtype.val '' J
  let B := Subtype.val '' (Jᶜ : Set ↥(Iᶜ:Set X))
  have count : A.ncard=J.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have leftover : B.ncard=Jᶜ.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have total := Set.ncard_add_ncard_compl J
  change J.ncard+Jᶜ.ncard=Iᶜ.ncard at total
  have newInd : Q.IsIndepSet A := by
    rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
    exact stand hv hw (fun eq => ne (congrArg Subtype.val eq)) edge
  refine ⟨A,⟨newInd,fun v _ => reg v,?_⟩,by omega⟩
  intro v _
  by_cases inI : v∈I
  · right
    by_contra! none
    have all : Q.neighborSet v⊆B := by
      intro w adj
      have away : w∉I := fun mem => ind inI mem (Q.ne_of_adj adj) adj
      let y:↥(Iᶜ:Set X) := ⟨w,away⟩
      have out : y∉J := fun mem => none w ⟨y,mem,rfl⟩ adj
      exact ⟨y,out,rfl⟩
    have bound := Set.ncard_le_ncard all
    have degree : (Q.neighborSet v).ncard=6 := reg v
    omega
  · let y:↥(Iᶜ:Set X) := ⟨v,inI⟩
    by_cases member:y∈J
    · exact Or.inl ⟨y,member,rfl⟩
    · obtain ⟨w,hw,edge⟩ := controls y member
      exact Or.inr ⟨w.val,⟨w,hw,rfl⟩,edge⟩

#print axioms short_stage_odd_six_regular
end JSP452Audit.StarHost
