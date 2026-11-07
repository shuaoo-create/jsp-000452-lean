import DetachedPairRootProfile
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem fully_matched_odd_part_exits (Q : SimpleGraph X) (M : Q.Subgraph)
    (hm : M.IsMatching) (T I : Set X) (odd : Odd T.ncard) (used : T⊆M.verts)
    (ext : ∀a∈T,∀b,Q.Adj a b → b∉T → b∈I) :
    ∃p∈T,∃u∈I,M.Adj u p := by
  classical
  by_contra none
  have closed (a b : X) (ha : a∈T) (ab : M.Adj a b) : b∈T := by
    by_contra out
    exact none ⟨a,ha,b,ext a ha b (M.adj_sub ab) out,ab.symm⟩
  have restricted : (M.induce T).IsMatching := by
    intro a ha
    obtain ⟨b,edge,uniq⟩ := hm (used ha)
    exact ⟨b,⟨ha,closed a b ha edge,edge⟩,fun w h => uniq w h.2.2⟩
  have card := matching_vertices_eq_twice_edges restricted
  change T.ncard=2*(M.induce T).edgeSet.ncard at card
  have parity := Nat.odd_iff.mp odd
  omega

/-- A matching exposing one root must send exactly one root partner into
each of the two odd regions. The singleton partners and the two odd exits
already exhaust the original root set minus the exposed root. -/
theorem unique_preferred_matching_exit (Q : SimpleGraph X) (I S P C : Set X)
    (ind : Q.IsIndepSet I) (i : X) (hi : i∈I) (M : Q.Subgraph) (hm : M.IsMatching)
    (support : M.verts={v | v≠i}) (count : S.ncard+3=I.ncard)
    (sp : Disjoint S P) (sc : Disjoint S C) (pc : Disjoint P C)
    (sOut : S⊆Iᶜ) (pOut : P⊆Iᶜ) (cOut : C⊆Iᶜ) (op : Odd P.ncard) (oc : Odd C.ncard)
    (singles : ∀s∈S,∀v,Q.Adj s v → v∈I)
    (pExt : ∀a∈P,∀b,Q.Adj a b → b∉P → b∈I)
    (cExt : ∀a∈C,∀b,Q.Adj a b → b∉C → b∈I) :
    ∃u∈I,u≠i ∧ ∃p∈P,M.Adj u p ∧ ∀a∈P,∀b∈I,M.Adj a b → b=u := by
  classical
  let W := independentMateLabels Q I i M
  have used (T : Set X) (outside:T⊆Iᶜ) : T⊆M.verts := by
    intro v hv
    rw [support];exact fun eq => outside hv (eq.symm ▸ hi)
  have usedNe {a b} (edge:M.Adj a b) : a≠i := by
    have h := M.edge_vert edge
    rwa [support] at h
  obtain ⟨p,hp,u,hu,up⟩ := fully_matched_odd_part_exits Q M hm P I op (used P pOut) pExt
  obtain ⟨c,hc,w,hw,wc⟩ := fully_matched_odd_part_exits Q M hm C I oc (used C cOut) cExt
  have ne : p≠c := fun eq => Set.disjoint_left.mp pc hp (eq.symm ▸ hc)
  have sSub : S⊆W := by
    intro v hv
    obtain ⟨b,edge,_⟩ := hm (used S sOut hv)
    exact ⟨sOut hv,b,singles v hv b (M.adj_sub edge),usedNe edge.symm,edge.symm⟩
  have pW : p∈W := ⟨pOut hp,u,hu,usedNe up,up⟩
  have cW : c∈W := ⟨cOut hc,w,hw,usedNe wc,wc⟩
  have sub : S∪{p,c}⊆W := by
    rintro v (hs|h)
    · exact sSub hs
    · rcases Set.mem_insert_iff.mp h with eq|eq
      · exact eq.symm ▸ pW
      · exact (Set.mem_singleton_iff.mp eq).symm ▸ cW
  have dis : Disjoint S ({p,c} : Set X) := by
    apply Set.disjoint_left.mpr
    intro v hv h
    rcases Set.mem_insert_iff.mp h with eq|eq
    · exact Set.disjoint_left.mp sp hv (eq.symm ▸ hp)
    · exact Set.disjoint_left.mp sc hv ((Set.mem_singleton_iff.mp eq).symm ▸ hc)
  have wCard : W.ncard+1=I.ncard := independentMateLabels_card Q I ind i hi M hm support
  have exactW : S∪{p,c}=W := by
    apply Set.eq_of_subset_of_ncard_le sub
    rw [Set.ncard_union_eq dis,Set.ncard_pair ne];omega
  refine ⟨u,hu,usedNe up,p,hp,up,?_⟩
  intro a ha b hb edge
  have aw : a∈W := ⟨pOut ha,b,hb,usedNe edge.symm,edge.symm⟩
  rw [←exactW] at aw
  rcases aw with hs|h
  · exact (Set.disjoint_left.mp sp hs ha).elim
  · rcases Set.mem_insert_iff.mp h with eq|eq
    · subst a;exact hm.eq_of_adj_left edge up.symm
    · exact (Set.disjoint_left.mp pc ha ((Set.mem_singleton_iff.mp eq).symm ▸ hc)).elim

#print axioms unique_preferred_matching_exit
end JSP452Audit.StarHost
