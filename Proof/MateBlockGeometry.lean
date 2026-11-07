import HeavyMateLocal

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The hole w together with both endpoints of each actual matched edge
whose endpoints are nonheavy and at least one of which touches w. -/
def mateBlock {X : Type*} (H : SimpleGraph X) (N : H.Subgraph) (w : X) : Set X :=
  {x | x=w ∨ ∃ y, N.Adj x y ∧ ¬holeHeavy H N x ∧ ¬holeHeavy H N y ∧
    (H.Adj w x ∨ H.Adj w y)}

theorem mem_mateBlock {X : Type*} (H : SimpleGraph X) (N : H.Subgraph) (w x : X) :
    x∈mateBlock H N w ↔ x=w ∨ ∃y, N.Adj x y ∧ ¬holeHeavy H N x ∧ ¬holeHeavy H N y ∧
      (H.Adj w x ∨ H.Adj w y) := Iff.rfl

theorem mateBlock_self {X : Type*} (H : SimpleGraph X) (N : H.Subgraph) (w : X) :
    w∈mateBlock H N w := Or.inl rfl

theorem mateBlock_pair_mem {X : Type*} (H : SimpleGraph X) (N : H.Subgraph) (w : X)
    {a b : X} (edge : N.Adj a b) (lightA : ¬holeHeavy H N a) (lightB : ¬holeHeavy H N b)
    (touch : H.Adj w a ∨ H.Adj w b) : a∈mateBlock H N w ∧ b∈mateBlock H N w :=
  ⟨Or.inr ⟨b,edge,lightA,lightB,touch⟩,Or.inr ⟨a,edge.symm,lightB,lightA,touch.symm⟩⟩

/-- Every label in the block is reachable internally from w in at most two
edges: go straight to an adjacent endpoint or via its actual matching partner. -/
theorem mateBlock_connected {X : Type*} (H : SimpleGraph X) (N : H.Subgraph) (w : X) :
    (H.induce (mateBlock H N w)).Connected := by
  let T := mateBlock H N w
  let anchor : T := ⟨w,mateBlock_self H N w⟩
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨anchor,?_⟩
  intro x
  rcases x.property with same | ⟨y,xy,lightX,lightY,touch⟩
  · have eq : x=anchor := Subtype.ext same
    exact eq.symm ▸ Reachable.refl anchor
  · let b : T := ⟨y,(mateBlock_pair_mem H N w xy lightX lightY touch).2⟩
    rcases touch with direct | viaMate
    · exact (show (H.induce T).Adj anchor x from direct).reachable
    · exact (show (H.induce T).Adj anchor b from viaMate).reachable.trans
        (show (H.induce T).Adj b x from (N.adj_sub xy).symm).reachable

/-- On the original-label set T minus w, the restriction of N is an actual
perfect matching with exactly its old adjacencies between surviving endpoints. -/
theorem mateBlock_perfect_off_root {X : Type*} (H : SimpleGraph X) (N : H.Subgraph)
    (matching : N.IsMatching) (w : X) (hole : w∉N.verts) :
    ∃ P : (H.induce (mateBlock H N w\{w})).Subgraph, P.IsPerfectMatching ∧
      ∀x y, P.Adj x y ↔ N.Adj x.val y.val := by
  let U := mateBlock H N w\{w}
  let P : (H.induce U).Subgraph := {
    verts := Set.univ
    Adj x y := N.Adj x.val y.val
    adj_sub := fun edge => N.adj_sub edge
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ edge => edge.symm⟩ }
  refine ⟨P,Subgraph.isPerfectMatching_iff.mpr ?_,fun _ _ => Iff.rfl⟩
  intro x
  have notRoot : x.val≠w := x.property.2
  obtain ⟨y,xy,lightX,lightY,touch⟩ := x.property.1.resolve_left notRoot
  have inBlock := (mateBlock_pair_mem H N w xy lightX lightY touch).2
  have away : y≠w := fun same => hole (same ▸ N.edge_vert xy.symm)
  let b : U := ⟨y,inBlock,away⟩
  exact ⟨b,xy,fun z edge => Subtype.ext (matching.eq_of_adj_left edge xy)⟩

/-- Every finite block has odd order, including a singleton hole with no
selected matching edge. -/
theorem mateBlock_odd {X : Type*} [Finite X] (H : SimpleGraph X) (N : H.Subgraph)
    (matching : N.IsMatching) (w : X) (hole : w∉N.verts) :
    Odd (mateBlock H N w).ncard := by
  obtain ⟨P,perfect,_⟩ := mateBlock_perfect_off_root H N matching w hole
  have pairs := matching_vertices_eq_twice_edges perfect.1
  rw [Subgraph.isSpanning_iff.mp perfect.2,Set.ncard_univ,Nat.card_coe_set_eq] at pairs
  have total := Set.ncard_sdiff_singleton_add_one (mateBlock_self H N w)
  exact ⟨P.edgeSet.ncard,by omega⟩

#print axioms mateBlock_connected
#print axioms mateBlock_perfect_off_root
#print axioms mateBlock_odd
end JSP452Audit.StarHost
