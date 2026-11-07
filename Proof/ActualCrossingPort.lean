import UniqueUnexposableVertex
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem clique_block_critical (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (u : X) (hu : u ∉ N.verts) (cl : H.IsClique (mateBlock H N u)) :
    PerfectAfterEveryDeletion (H.induce (mateBlock H N u)) := by
  apply critical_of_odd_small_alpha
  · simpa only [Nat.card_coe_set_eq] using mateBlock_odd H N hm u hu
  · intro a b c ab _ _
    exact Or.inl (cl a.property b.property (fun eq => ab (Subtype.ext eq)))
  · intro v a b
    by_cases eq : a=b
    · exact eq ▸ Reachable.refl a
    · have ne : a.val.val ≠ b.val.val := fun h => eq (Subtype.ext (Subtype.ext h))
      exact (show ((H.induce (mateBlock H N u)).induce {z | z≠v}).Adj a b from
        cl a.val.property b.val.property ne).reachable

theorem crossing_preferred_endpoint_not_exposable (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    {w u : X} (hw : w∉N.verts) (hu : u∉N.verts) (ne : w≠u)
    (cl : H.IsClique (mateBlock H N u))
    (x : ↥(mateBlock H N w ∪ zeroMateRegion H N)) (y : mateBlock H N u)
    (edge : H.Adj x.val y.val) :
    ¬ExposablePoint (H.induce (mateBlock H N w ∪ zeroMateRegion H N)) x := by
  intro ex
  exact preferred_union_exposed_no_cross H N hm maximum hw hu ne x y ex
    (clique_block_critical H N hm u hu cl y) edge

/-- For one connected preferred union of the same maximum matching, every
edge crossing to a distinct clique block has the same preferred endpoint. -/
theorem crossings_share_preferred_endpoint (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (w : X) (hw : w∉N.verts)
    (conn : (H.induce (mateBlock H N w ∪ zeroMateRegion H N)).Preconnected)
    (limit : ∀ S : Set X, H.IsIndepSet S → S.ncard≤N.vertsᶜ.ncard+1)
    (u v : X) (hu : u∉N.verts) (hv : v∉N.verts) (wu : w≠u) (wv : w≠v)
    (cu : H.IsClique (mateBlock H N u)) (cv : H.IsClique (mateBlock H N v))
    (x z : ↥(mateBlock H N w ∪ zeroMateRegion H N))
    (a : mateBlock H N u) (b : mateBlock H N v)
    (first : H.Adj x.val a.val) (second : H.Adj z.val b.val) : z = x := by
  have one := crossing_preferred_endpoint_not_exposable H N hm maximum hw hu wu cu x a first
  have two := crossing_preferred_endpoint_not_exposable H N hm maximum hw hv wv cv z b second
  have odd := preferred_region_odd H N hm w hw
  rw [←Nat.card_coe_set_eq] at odd
  by_contra ne
  exact two (every_other_vertex_exposable _ conn odd
    (block_with_zero_region_small H N hm maximum w hw limit) x one z ne)

#print axioms crossings_share_preferred_endpoint
end JSP452Audit.StarHost
