import MateBlockGeometry
import NoThreeAugment

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem heavy_of_two_holes {X : Type*} [Finite X] (H : SimpleGraph X)
    (N : H.Subgraph) {a w u : X} (hw : w∉N.verts) (hu : u∉N.verts)
    (distinct : w≠u) (wa : H.Adj w a) (au : H.Adj a u) : holeHeavy H N a := by
  have sub : ({w,u} : Set X) ⊆ H.neighborSet a ∩ N.vertsᶜ := by
    rintro v (eq|eq)
    · exact eq.symm ▸ ⟨wa.symm,hw⟩
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ ⟨au,hu⟩
  have size := Set.ncard_le_ncard sub
  rwa [Set.ncard_pair distinct] at size

/-- In the same residual graph, no vertex of the local block has an edge to
an exposed vertex other than its root. A second contact on the touching
endpoint is heavy; contact across the matched edge gives a length-three
augmenting path. -/
theorem mateBlock_separated {X : Type*} [Finite X] (H : SimpleGraph X)
    (N : H.Subgraph) (matching : N.IsMatching)
    (maximum : N.edgeSet.ncard=matchingEdges H) {w : X} (hw : w∉N.verts) :
    ∀ x∈mateBlock H N w, ∀ u∈N.vertsᶜ \ {w}, ¬H.Adj x u := by
  intro x hx u hu edge
  have distinct : w≠u := fun eq => hu.2 (Set.mem_singleton_iff.mpr eq.symm)
  rcases (mem_mateBlock H N w x).mp hx with root|⟨y,xy,lightX,_,touch⟩
  · subst x
    exact hu.1 (missed_neighbors_subset H N matching maximum hw edge)
  · rcases touch with wx|wy
    · exact lightX (heavy_of_two_holes H N hw hu.1 distinct wx edge)
    · exact no_three_augment H N matching maximum hu.1 hw distinct.symm xy edge.symm wy.symm

/-- The only exposed vertex the block can contain is its root. -/
theorem mateBlock_disjoint_other_holes {X : Type*} (H : SimpleGraph X)
    (N : H.Subgraph) (w : X) :
    Disjoint (mateBlock H N w) (N.vertsᶜ \ {w}) := by
  apply Set.disjoint_left.mpr
  intro x hx other
  rcases (mem_mateBlock H N w x).mp hx with root|⟨y,xy,_⟩
  · exact other.2 (Set.mem_singleton_iff.mpr root)
  · exact other.1 (N.edge_vert xy)

private theorem inducedIndependent_image {X : Type*} (H : SimpleGraph X)
    (T : Set X) (K : Set T) (indK : (H.induce T).IsIndepSet K) :
    H.IsIndepSet (Subtype.val '' K) := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ different edge
  exact indK hx hy (fun eq => different (congrArg Subtype.val eq)) edge

/-- If W is one below an independence bound, an independent set within a
block disjoint and nonadjacent to W except at w uses at most two vertices.
The input set K lives in the induced graph on the actual block. -/
theorem independent_set_in_separated_block_le_two {X : Type*} [Finite X]
    (H : SimpleGraph X) (W T : Set X) (w : X) (hw : w∈W)
    (indW : H.IsIndepSet W) (limit : ∀A : Set X,H.IsIndepSet A → A.ncard≤W.ncard+1)
    (apart : Disjoint T (W \ {w}))
    (separated : ∀ x∈T, ∀u∈W \ {w},¬H.Adj x u)
    (K : Set T) (indK : (H.induce T).IsIndepSet K) : K.ncard≤2 := by
  let A : Set X := Subtype.val '' K
  have into : A⊆T := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have noOverlap : Disjoint A (W \ {w}) := apart.mono_left into
  have independentA := inducedIndependent_image H T K indK
  have joined : H.IsIndepSet (A ∪ (W \ {w})) := by
    rintro x (hx|hx) y (hy|hy) ne edge
    · exact independentA hx hy ne edge
    · exact separated x (into hx) y hy edge
    · exact separated y (into hy) x hx edge.symm
    · exact indW hx.1 hy.1 ne edge
  have count := limit (A ∪ (W \ {w})) joined
  rw [Set.ncard_union_eq noOverlap] at count
  have labels : A.ncard=K.ncard := Set.ncard_image_of_injective K Subtype.val_injective
  have removed := Set.ncard_sdiff_singleton_add_one hw
  omega

/-- Apply the independent-set bound of the original Q to the actual block
of the maximum matching that remains in Q-I. All vertices keep their labels
through both inductions. -/
theorem actual_mateBlock_independent_bound {X : Type*} [Finite X] (Q : SimpleGraph X)
    (I : Set X) (N : (Q.induce Iᶜ).Subgraph) (matching : N.IsMatching)
    (maximum : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (w : ↥(Iᶜ : Set X)) (hw : w∉N.verts)
    (globalI : ∀ A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (gap : N.vertsᶜ.ncard+1=I.ncard)
    (K : Set (mateBlock (Q.induce Iᶜ) N w))
    (indK : ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N w)).IsIndepSet K) :
    K.ncard≤2 := by
  let H := Q.induce Iᶜ
  have indW : H.IsIndepSet N.vertsᶜ := by
    intro a ha b hb _ edge
    exact hb (missed_neighbors_subset H N matching maximum ha edge)
  have limit (A : Set ↥(Iᶜ : Set X)) (independent : H.IsIndepSet A) :
      A.ncard≤N.vertsᶜ.ncard+1 := by
    have bound := globalI (Subtype.val '' A) (inducedIndependent_image Q Iᶜ A independent)
    rwa [Set.ncard_image_of_injective A Subtype.val_injective,←gap] at bound
  exact independent_set_in_separated_block_le_two H N.vertsᶜ (mateBlock H N w) w hw
    indW limit (mateBlock_disjoint_other_holes H N w) (mateBlock_separated H N matching maximum hw) K indK

#print axioms mateBlock_separated
#print axioms mateBlock_disjoint_other_holes
#print axioms independent_set_in_separated_block_le_two
#print axioms actual_mateBlock_independent_bound
end JSP452Audit.StarHost

