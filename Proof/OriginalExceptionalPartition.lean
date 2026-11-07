import ExceptionalOriginalSizes
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- The actual unpaid large-degree component supplies one heavy edge,
including its orientation, the partition of the residual labels, and the
classification of its possible part sizes. -/
theorem unpaid_exceptional_clique_partition (Q : SimpleGraph X) (D k : ℕ)
    (six : 6≤D) (conn : Q.Connected) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (fail : envelopeReserve Q k<minimumExposure Q D) :
    ∃ (I : Set X) (v : X) (M : Q.Subgraph),
      Q.IsIndepSet I ∧ (∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard) ∧ 3≤I.ncard ∧ v∈I ∧
      M.IsMatching ∧ M.verts={u|u≠v} ∧ M.edgeSet.ncard=matchingEdges Q ∧
      let H := Q.induce Iᶜ
      let N := restrictedOutsideMatching Q I M
      N.IsMatching ∧ N.edgeSet.ncard=matchingEdges H ∧ N.vertsᶜ.ncard+1=I.ncard ∧
      H.IsClique (mateAntineighborhood H N.vertsᶜ) ∧
      ∃a b,holeHeavy H N a ∧ N.Adj a b ∧ exceptionalMateRegion H N={a,b} ∧
        let F := exceptionalParts H N b
        (∀i j,i≠j → Disjoint (F i) (F j)) ∧ (∀i,H.IsClique (F i)) ∧
        (∀i,a∉F i) ∧ (∀u,u≠a → ∃i,u∈F i) ∧
        (∀i j,i≠j → ∀u∈F i,∀w∈F j,¬H.Adj u w) ∧
        ((∀i,(F i).ncard=1) ∨ ∃l,(F l).ncard=D-1 ∧
          (∀i,i≠l → (F i).ncard=1) ∧ ∃u w,u≠w ∧ u∉F l ∧ w∉F l ∧ H.Adj a u ∧ H.Adj a w) := by
  obtain ⟨I,v,M,ind,largest,three,vi,hm,supp,opt,hn,max,exceptional⟩ :=
    unpaid_large_component_requires_exception Q D k six conn reg crit fail
  let H := Q.induce Iᶜ
  let N := restrictedOutsideMatching Q I M
  have exp := regular_factorCritical_exposure Q crit v D reg
  have env := (envelope_reserve_account Q D).2
  have trunc := envelopeReserve_le_truncation Q D k (fun u => (reg u).le)
  have zero : baseReserve Q D=0 := by omega
  have ord := factorCritical_order_rank Q crit v
  have par := regular_even_on_odd Q D (show Odd (Nat.card X) from ⟨matchingEdges Q,by omega⟩) reg
  have anti := (residual_mate_clique Q D (by omega) reg crit zero I ind largest v vi M hm supp).2.2
  obtain ⟨_,_,labels,count,_⟩ := independent_mate_barrier Q D (by omega) reg crit zero I ind v vi M hm supp
  -- Recover the cardinal equality on the original chosen matching.
  have gap : N.vertsᶜ.ncard+1=I.ncard := by
    rwa [←labels,Set.ncard_image_of_injective _ Subtype.val_injective] at count
  have non := Set.nonempty_iff_ne_empty.mpr exceptional
  obtain ⟨x,y,xy,hot⟩ := non
  obtain ⟨a,b,heavy,ab⟩ : ∃a b,holeHeavy H N a ∧ N.Adj a b := by
    rcases hot with hx|hy
    · exact ⟨x,y,hx,xy⟩
    · exact ⟨y,x,hy,xy.symm⟩
  have limit (U:Set ↥(Iᶜ : Set X)) (si:H.IsIndepSet U) : U.ncard≤N.vertsᶜ.ncard+1 := by
    have imageInd : Q.IsIndepSet (Subtype.val '' U) := by
      rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
      exact si hv hw (fun eq => ne (congrArg Subtype.val eq)) edge
    have cap := largest _ imageInd
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
  obtain ⟨pair,dis,cl,_,out,cover,sep⟩ := exceptional_cut_partition H N hn max limit anti heavy ab
  have sizes := exceptional_original_sizes Q I ind largest D (by omega) par reg N hn max gap anti heavy ab
  exact ⟨I,v,M,ind,largest,three,vi,hm,supp,opt,hn,max,gap,anti,a,b,heavy,ab,pair,dis,cl,out,cover,sep,sizes⟩

#print axioms unpaid_exceptional_clique_partition
end JSP452Audit.StarHost
