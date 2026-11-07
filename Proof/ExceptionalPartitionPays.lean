import ReserveExceptDegreeFour
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- This uses a supplied genuine exceptional matched edge; in particular it
also covers degree four without invoking the large-degree extraction. -/
theorem exceptional_partition_positive (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ)) (gap : N.vertsᶜ.ncard+1=I.ncard)
    (anti : (Q.induce Iᶜ).IsClique (mateAntineighborhood (Q.induce Iᶜ) N.vertsᶜ))
    (existsEx : exceptionalMateRegion (Q.induce Iᶜ) N≠∅) : 1≤baseReserve Q D := by
  classical
  let H := Q.induce Iᶜ
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set X))
  let _ := Fintype.ofFinite J
  obtain ⟨u,v,edge,hot⟩ := Set.nonempty_iff_ne_empty.mpr existsEx
  obtain ⟨a,b,heavy,ab⟩ : ∃a b,holeHeavy H N a ∧ N.Adj a b := by
    rcases hot with ha|hb
    · exact ⟨u,v,ha,edge⟩
    · exact ⟨v,u,hb,edge.symm⟩
  let F := exceptionalParts H N b
  have limit (U:Set ↥(Iᶜ : Set X)) (si:H.IsIndepSet U) : U.ncard≤N.vertsᶜ.ncard+1 := by
    have imageInd : Q.IsIndepSet (Subtype.val '' U) := by
      rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne e
      exact si hv hw (fun eq => ne (congrArg Subtype.val eq)) e
    have cap := largest _ imageInd
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
  obtain ⟨_,dis,cl,_,off,cover,sep⟩ := exceptional_cut_partition H N hm max limit anti heavy ab
  have card : Fintype.card (Option J)=I.ncard := by
    rw [Fintype.card_option,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq];exact gap
  rcases exceptional_original_sizes Q I ind largest D four par reg N hm max gap anti heavy ab with
    single|⟨q,sz,others,two⟩
  · exact exceptional_singletons_positive Q I ind D four reg crit a F card dis off cover sep single
  · obtain ⟨s,_,_⟩ := lift_exceptional_big_clique Q I D a F card dis off cover sep q (cl q) sz others two
    exact exceptional_large_clique_positive Q I ind largest D four par reg crit s

#print axioms exceptional_partition_positive
end JSP452Audit.StarHost
