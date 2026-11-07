import ExceptionalMatchedBarrier
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A heavy matched edge forces every ordinary mate block to be a clique,
separated from the odd clique consisting of the zero region and its partner. -/
theorem exceptional_parts_are_separated (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (limit : ∀T:Set X,H.IsIndepSet T → T.ncard≤N.vertsᶜ.ncard+1)
    (anti : H.IsClique (mateAntineighborhood H N.vertsᶜ))
    {a b : X} (heavy : holeHeavy H N a) (ab : N.Adj a b) :
    let K := zeroMateRegion H N∪{b}
    H.IsClique K ∧ Odd K.ncard ∧ ∀j,j∉N.verts →
      H.IsClique (mateBlock H N j) ∧ (∀v∈mateBlock H N j,∀z∈K,¬H.Adj v z) := by
  intro K
  obtain ⟨clK,oddK,barrier⟩ := exceptional_partner_exposure_barrier H N hm maximum anti heavy ab
  refine ⟨clK,oddK,?_⟩
  intro j hj
  let T := mateBlock H N j
  let U := T∪K
  have be : b∈exceptionalMateRegion H N := ⟨a,ab.symm,Or.inr heavy⟩
  have bfree : b∉T := fun h => Set.disjoint_left.mp (mate_block_disjoint_exceptional H N hm j hj) h be
  have bk : b∈K := Or.inr (Set.mem_singleton _)
  have kSub : K⊆mateAntineighborhood H N.vertsᶜ := by
    rintro v (hz|eq)
    · exact zeroMateRegion_subset_anti H N hz
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ holeHeavy_partner_mem_antineighborhood H N hm maximum heavy ab
  have indW : H.IsIndepSet N.vertsᶜ := fun _ hx _ hy _ edge => hy (missed_neighbors_subset H N hm maximum hx edge)
  have small : NoIndependentTriple (H.induce U) := by
    apply noIndependentTriple_of_set_bound
    apply independent_set_in_separated_block_le_two H N.vertsᶜ U j hj indW limit
    · apply Set.disjoint_left.mpr
      rintro v (ht|hk) hu
      · exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N j) ht hu
      · exact (kSub hk).1 hu.1
    · rintro v (ht|hk) u hu adj
      · exact mateBlock_separated H N hm maximum hj v ht u hu adj
      · exact (kSub hk).2 u hu.1 adj
  have clique : H.IsClique T := by
    by_contra wrong
    have bad : ¬(H.induce T).IsClique Set.univ := by
      intro yes
      apply wrong
      intro v hv w hw ne
      exact @yes ⟨v,hv⟩ (Set.mem_univ _) ⟨w,hw⟩ (Set.mem_univ _)
        (fun eq => ne (congrArg Subtype.val eq))
    have seed : ∃v,ExposablePoint (H.induce T) v :=
      ⟨⟨j,mateBlock_self H N j⟩,mate_block_root_exposable H N hm j hj⟩
    obtain ⟨v,w,ne,vw,ev,ew⟩ := exposable_pair_in_nonclique (H.induce T)
      (mateBlock_connected H N j) seed bad
    let v' : U := ⟨v.val,Or.inl v.property⟩
    let w' : U := ⟨w.val,Or.inl w.property⟩
    let b' : U := ⟨b,Or.inr bk⟩
    have diff : v'≠w' := fun eq => ne (Subtype.ext (show v.val=w.val from congrArg (fun t:U => t.val) eq))
    have diffV : v'≠b' := by
      intro h; have eq : v.val=b := congrArg (fun t:U => t.val) h
      exact bfree (eq ▸ (show v.val∈T from v.property))
    have diffW : w'≠b' := by
      intro h; have eq : w.val=b := congrArg (fun t:U => t.val) h
      exact bfree (eq ▸ (show w.val∈T from w.property))
    rcases small v' w' b' diff diffV diffW with edge|edge|edge
    · exact vw edge
    · exact barrier j hj v ev ⟨b,bk⟩ edge
    · exact barrier j hj w ew ⟨b,bk⟩ edge
  refine ⟨clique,?_⟩
  intro v hv z hz
  have full := odd_clique_exposes_each H T clique (mateBlock_odd H N hm j hj)
  exact barrier j hj ⟨v,hv⟩ (full ⟨v,hv⟩) ⟨z,hz⟩

#print axioms exceptional_parts_are_separated
end JSP452Audit.StarHost
