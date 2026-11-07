import UniqueMateException
import MateBlockSeparation
import ZeroMateRegion
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Both endpoints of every exceptional actual matching edge. -/
def exceptionalMateRegion (H : SimpleGraph X) (N : H.Subgraph) : Set X :=
  {a | ∃ b, N.Adj a b ∧ (holeHeavy H N a ∨ holeHeavy H N b)}

/-- Under the unique heavy-endpoint bound this region is either empty
or exactly the two distinct endpoints of one matching edge. -/
theorem exceptional_region_empty_or_pair (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (unique : ∀a b,holeHeavy H N a → holeHeavy H N b → a=b) :
    exceptionalMateRegion H N=∅ ∨ ∃a b,N.Adj a b ∧ a≠b ∧
      exceptionalMateRegion H N={a,b} := by
  classical
  by_cases ne : (exceptionalMateRegion H N).Nonempty
  · right
    obtain ⟨u,v,uv,h⟩ := ne
    have oriented : ∃a b,N.Adj a b ∧ holeHeavy H N a := by
      rcases h with hu|hv
      · exact ⟨u,v,uv,hu⟩
      · exact ⟨v,u,uv.symm,hv⟩
    obtain ⟨a,b,ab,ha⟩ := oriented
    refine ⟨a,b,ab,(N.adj_sub ab).ne,?_⟩
    ext z
    constructor
    · rintro ⟨y,zy,hz|hy⟩
      · exact Or.inl (unique z a hz ha)
      · have ya := unique y a hy ha
        subst y
        exact Or.inr (hm.eq_of_adj_left zy.symm ab)
    · rintro (rfl|eq)
      · exact ⟨b,ab,Or.inl ha⟩
      · have e : z=b := eq
        subst z
        exact ⟨a,ab.symm,Or.inr ha⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp ne)

theorem mate_block_disjoint_zero (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) : Disjoint (mateBlock H N w) (zeroMateRegion H N) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y,xy,awayX,awayY⟩
  rcases hx with eq|⟨z,xz,_,_,touch⟩
  · exact hw (eq ▸ N.edge_vert xy)
  · have zy := hm.eq_of_adj_left xz xy
    subst z
    exact touch.elim (fun t => awayX w hw t.symm) (fun t => awayY w hw t.symm)

theorem mate_block_disjoint_exceptional (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) : Disjoint (mateBlock H N w) (exceptionalMateRegion H N) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨y,xy,hy⟩
  rcases hx with eq|⟨z,xz,lightX,lightZ,_⟩
  · exact hw (eq ▸ N.edge_vert xy)
  · have zy := hm.eq_of_adj_left xz xy
    subst z
    exact hy.elim lightX lightZ

theorem zero_region_disjoint_exceptional [Finite X] (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) : Disjoint (zeroMateRegion H N) (exceptionalMateRegion H N) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨y,xy,awayX,awayY⟩ ⟨z,xz,heavy⟩
  have zy := hm.eq_of_adj_left xz xy
  subst z
  rcases heavy with hx|hy
  · obtain ⟨w,hw,wx,_⟩ := holeHeavy_exposed_neighbor_ne H N hx x
    exact awayX w hw wx.symm
  · obtain ⟨w,hw,wy,_⟩ := holeHeavy_exposed_neighbor_ne H N hy y
    exact awayY w hw wy.symm

/-- Blocks belonging to distinct actual holes share no labels. -/
theorem different_mate_blocks_disjoint [Finite X] (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (w u : X) (hw : w∉N.verts) (hu : u∉N.verts)
    (ne : w≠u) : Disjoint (mateBlock H N w) (mateBlock H N u) := by
  apply Set.disjoint_left.mpr
  intro x hx xu
  have other : u ∈ N.vertsᶜ \ {w} := ⟨hu,fun eq => ne (Set.mem_singleton_iff.mp eq).symm⟩
  rcases xu with eq | ⟨y,xy,_,_,touch⟩
  · subst x
    exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N w) hx other
  · rcases hx with eq | ⟨z,xz,lx,lz,t⟩
    · exact hw (eq ▸ N.edge_vert xy)
    · have zy := hm.eq_of_adj_left xz xy
      subst z
      have pair := mateBlock_pair_mem H N w xy lx lz t
      exact touch.elim (fun a => mateBlock_separated H N hm max hw x pair.1 u other a.symm)
        (fun a => mateBlock_separated H N hm max hw y pair.2 u other a.symm)

/-- Every residual label is in one of the three classes. This includes
isolated holes, blocks with a single point, and zero exceptional edges. -/
theorem mate_classes_cover (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching) (x : X) :
    (∃w,w∉N.verts ∧ x∈mateBlock H N w) ∨ x∈zeroMateRegion H N ∨ x∈exceptionalMateRegion H N := by
  classical
  by_cases hx : x∈N.verts
  · obtain ⟨y,xy,_⟩ := hm hx
    by_cases exceptional : holeHeavy H N x ∨ holeHeavy H N y
    · exact Or.inr (Or.inr ⟨y,xy,exceptional⟩)
    push Not at exceptional
    by_cases touch : ∃w,w∉N.verts ∧ (H.Adj w x ∨ H.Adj w y)
    · obtain ⟨w,hw,adj⟩ := touch
      exact Or.inl ⟨w,hw,(mateBlock_pair_mem H N w xy exceptional.1 exceptional.2 adj).1⟩
    · refine Or.inr (Or.inl ⟨y,xy,?_,?_⟩)
      · intro w hw edge; exact touch ⟨w,hw,Or.inl edge.symm⟩
      · intro w hw edge; exact touch ⟨w,hw,Or.inr edge.symm⟩
  · exact Or.inl ⟨x,hx,mateBlock_self H N x⟩

#print axioms exceptional_region_empty_or_pair
#print axioms different_mate_blocks_disjoint
#print axioms mate_classes_cover
end JSP452Audit.StarHost
