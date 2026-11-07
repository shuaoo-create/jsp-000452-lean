import RootDebtOnTheSameNineCut
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem twice_edges_le_simple_order {X:Type*} [Finite X] (Q:SimpleGraph X) :
    2*Q.edgeSet.ncard≤Nat.card X*(Nat.card X-1) := by
  classical
  let _ := Fintype.ofFinite X
  have cap (x:X) : Q.degree x≤Nat.card X-1 := by have := Q.degree_lt_card_verts x;rw [←Nat.card_eq_fintype_card] at this;omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => cap x)
  rw [Q.sum_degrees_eq_twice_card_edges,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at sum
  have equal : Q.edgeFinset.card=Q.edgeSet.ncard := by rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card]
  rwa [equal] at sum

namespace NineOriginalCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)
structure Port (c:↥K.blocks) where
  tip : X
  root : X
  tip_mem : tip∈K.labels c
  root_mem : root∈K.S
  edge : G.Adj tip root
  only : ∀x∈K.labels c,∀y∉K.labels c,G.Adj x y → x=tip ∧ y=root

theorem unique_physical_port (c:↥K.blocks) (unit:c∈K.onePortBlocks) : Nonempty (K.Port c) := by
  classical
  let U := K.labels c
  let E : Set (↥U×↥K.S) := {p|G.Adj p.1.val p.2.val}
  have card : E.ncard=1 := unit.1
  obtain ⟨p,eq⟩ := Set.ncard_eq_one.mp card
  have edge : p∈E := eq.symm ▸ Set.mem_singleton p
  refine ⟨⟨p.1.val,p.2.val,p.1.property,p.2.property,edge,?_⟩⟩
  intro x mem y outside e
  have barrier : y∈K.barrier := by by_contra away;exact outside (cut_piece_neighbor G K.barrier c.val mem e away)
  have root : y∈K.S := barrier.resolve_right (fun hy => no_edge_when_port_zero G unit.2 mem hy e)
  let q : ↥U×↥K.S := (⟨x,mem⟩,⟨y,root⟩)
  have inE : q∈E := e
  rw [eq,Set.mem_singleton_iff] at inE
  exact ⟨congrArg (fun z:↥U×↥K.S => z.1.val) inE,congrArg (fun z:↥U×↥K.S => z.2.val) inE⟩

theorem actual_one_port_order (cap:∀x,Nat.card (G.neighborSet x)≤9) (c:↥K.blocks) (unit:c∈K.onePortBlocks) :
    Odd (Nat.card c.val.supp) ∧ 11≤Nat.card c.val.supp := by
  let U := K.labels c
  let n := Nat.card c.val.supp
  have size : n=U.ncard := Nat.card_congr (cutPieceVertexEquiv G K.barrier c.val)
  have odd := uniform_member_odd_size_boundary G 3 6 (by decide) K.S K.T c.val c.property
  change Odd (n+K.tPorts c) at odd
  rw [unit.2,Nat.add_zero] at odd
  have full (x) (hx:x∈U) := uniform_tight_piece_full G 3 6 cap K.S K.T c.val c.property x hx
  have cut := actual_cut_piece_boundary_to_roots G K.S K.T K.apart c.val
  change crossCount G U Uᶜ=K.sPorts c+K.tPorts c at cut
  rw [unit.1,unit.2,Nat.add_zero] at cut
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  rw [degree_sum_full G U 9 full,cut,←size] at hand
  have simple := twice_edges_le_simple_order (G.induce U)
  change 2*(G.induce U).edgeSet.ncard≤U.ncard*(U.ncard-1) at simple
  rw [←size] at simple
  refine ⟨odd,?_⟩
  change 11≤n
  by_contra! small
  obtain ⟨z,order⟩ := odd
  have low : n≤9 := by omega
  have many := Nat.mul_le_mul_left n (show n-1≤8 by omega)
  have one : n≤1 := by omega
  rw [show n-1=0 by omega,Nat.mul_zero] at simple
  omega

#print axioms unique_physical_port
#print axioms actual_one_port_order
end NineOriginalCut
#print axioms twice_edges_le_simple_order
end JSP452Audit.StarHost
