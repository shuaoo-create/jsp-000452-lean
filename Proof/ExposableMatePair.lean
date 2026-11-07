import CrossMateBlocks
import AlternatingFive
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def ExposablePoint (G : SimpleGraph X) (v : X) : Prop :=
  ∃P : (G.induce {z|z≠v}).Subgraph,P.IsPerfectMatching

omit [Finite X] in
theorem exposable_of_single_hole (G : SimpleGraph X) (v : X) (M : G.Subgraph)
    (hm : M.IsMatching) (support : M.verts={x|x≠v}) : ExposablePoint G v := by
  refine ⟨restrictMatched M v,Subgraph.isPerfectMatching_iff.mpr ?_⟩
  intro x
  have xin : x.val∈M.verts := by rw [support]; exact x.property
  obtain ⟨y,xy,_⟩ := hm xin
  have inside := M.edge_vert xy.symm
  rw [support] at inside
  exact ⟨⟨y,inside⟩,xy,fun z h => Subtype.ext (hm.eq_of_adj_left h xy)⟩

private theorem shift_exposable (G : SimpleGraph X) (M : G.Subgraph) (hm : M.IsMatching)
    (x : X) (support : M.verts={v|v≠x}) {a b : X} (ab : M.Adj a b) (xa : G.Adj x a) :
    ExposablePoint G b := by
  have hx : x∉M.verts := by rw [support]; exact fun h => h rfl
  have bx : b≠x := by have h := M.edge_vert ab.symm; rwa [support] at h
  obtain ⟨N,hn,_,verts,_,_⟩ := shift_matching_hole G M hm hx ab xa
  apply exposable_of_single_hole G b N hn
  rw [verts,support]
  ext u
  simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_ofPred_eq,Set.mem_singleton_iff]
  grind

/-- If all exposable labels form a clique, the set is closed under
adjacency: flipping a matched pair first exposes z, and then exposes y
using the edge from the original hole x to z. -/
private theorem exposable_clique_closed (G : SimpleGraph X)
    (cl : G.IsClique {v|ExposablePoint G v}) {x y} (ex : ExposablePoint G x)
    (xy : G.Adj x y) : ExposablePoint G y := by
  obtain ⟨P,perf⟩ := ex
  obtain ⟨M,hm,supp,_⟩ := lift_perfect_off_vertex_maximum G x P perf
  have yIn : y∈M.verts := supp ▸ xy.ne.symm
  obtain ⟨z,yz,_⟩ := hm yIn
  have zex := shift_exposable G M hm x supp yz xy
  have zx : z≠x := by have h := M.edge_vert yz.symm; rwa [supp] at h
  have xz := cl (show ExposablePoint G x from ⟨P,perf⟩) zex zx.symm
  exact shift_exposable G M hm x supp yz.symm xz

theorem exposable_pair_in_nonclique (G : SimpleGraph X) (conn : G.Connected)
    (seed : ∃w,ExposablePoint G w) (bad : ¬G.IsClique Set.univ) :
    ∃a b,a≠b ∧ ¬G.Adj a b ∧ ExposablePoint G a ∧ ExposablePoint G b := by
  classical
  by_contra! none
  have cl : G.IsClique {v|ExposablePoint G v} := by
    intro a ea b eb ne
    by_contra notEdge
    exact none a b ne notEdge ea eb
  have travel {u v : X} (p : G.Walk u v) : ExposablePoint G u → ExposablePoint G v := by
    induction p with
    | nil => exact id
    | cons edge tail ih => exact fun ex => ih (exposable_clique_closed G cl ex edge)
  obtain ⟨w,ew⟩ := seed
  have all (v : X) : ExposablePoint G v := by
    obtain ⟨p⟩ := conn.preconnected w v
    exact travel p ew
  exact bad (fun {u} _ {v} _ ne => cl (all u) (all v) ne)

omit [Finite X] in
/-- The distinguished vertex of the actual pointed block is exposable
in that same induced block. The other covered pairs stay on their labels. -/
theorem mate_block_root_exposable (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) :
    ExposablePoint (H.induce (mateBlock H N w)) ⟨w,mateBlock_self H N w⟩ := by
  let T := mateBlock H N w
  let r : T := ⟨w,mateBlock_self H N w⟩
  let P : (H.induce T).Subgraph := {
    verts := {a|a≠r}
    Adj a b := N.Adj a.val b.val
    adj_sub := fun h => N.adj_sub h
    edge_vert := by
      intro v b e eq
      have used := N.edge_vert e
      have ev : v.val=w := congrArg Subtype.val eq
      rw [ev] at used
      exact hw used
    symm := ⟨fun _ _ e => e.symm⟩ }
  apply exposable_of_single_hole _ r P _ rfl
  intro a ha
  have ne : a.val≠w := fun eq => ha (Subtype.ext eq)
  obtain ⟨b,ab,la,lb,t⟩ := a.property.resolve_left ne
  have bin := (mateBlock_pair_mem H N w ab la lb t).2
  exact ⟨⟨b,bin⟩,ab,fun z hz => Subtype.ext (hm.eq_of_adj_left hz ab)⟩

#print axioms exposable_pair_in_nonclique
#print axioms mate_block_root_exposable
end JSP452Audit.StarHost
