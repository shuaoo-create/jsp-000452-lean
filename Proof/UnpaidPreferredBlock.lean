import ChoosePreferredBlock
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- All inputs other than the explicitly stated branch conditions are
obtained from this unpaid original component and the same fixed matching. -/
theorem unpaid_preferred_block_connection (Q : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (fail : envelopeReserve Q k<minimumExposure Q D) :
    ∃ (I : Set X) (v : X) (M : Q.Subgraph),
      Q.IsIndepSet I ∧ (∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard) ∧ v∈I ∧
      M.IsMatching ∧ M.verts={x|x≠v} ∧ M.edgeSet.ncard=matchingEdges Q ∧
      let H := Q.induce Iᶜ
      let N := restrictedOutsideMatching Q I M
      let W := independentMateLabels Q I v M
      Subtype.val '' N.vertsᶜ=W ∧
      (exceptionalMateRegion H N=∅ →
        (∃u,u∉N.verts ∧ 3≤(mateBlock H N u).ncard) →
        ∃w,w.val∈W ∧ w∉N.verts ∧ 3≤(mateBlock H N w).ncard ∧
          (H.induce (mateBlock H N w ∪ zeroMateRegion H N)).Connected ∧
          ∀u,u∉N.verts → u≠w → H.IsClique (mateBlock H N u)) := by
  obtain ⟨I,v,M,ind,maxI,_,vi,mat,supp,maximum,hn,rank,_,labels,count,_,anti,_⟩ :=
    unpaid_regular_mate_decomposition Q D k large reg crit fail
  refine ⟨I,v,M,ind,maxI,vi,mat,supp,maximum,labels,?_⟩
  intro e b
  let H := Q.induce Iᶜ
  let N := restrictedOutsideMatching Q I M
  have odd : Odd (Nat.card X) := ⟨matchingEdges Q,by have h:=factorCritical_order_rank Q crit v;omega⟩
  have even := regular_even_on_odd Q D odd reg
  have clZ := (pullback_mate_antineighborhood_clique Q I N _ labels anti).subset (zeroMateRegion_subset_anti H N)
  have gap : N.vertsᶜ.ncard+1=I.ncard := by
    rwa [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at count
  obtain ⟨w,hw,big,joined,others⟩ :=
    exists_preferred_connected_block Q I ind maxI D even reg N hn rank gap e clZ b
  exact ⟨w,labels ▸ ⟨w,hw,rfl⟩,hw,big,joined,others⟩

#print axioms unpaid_preferred_block_connection
end JSP452Audit.StarHost
