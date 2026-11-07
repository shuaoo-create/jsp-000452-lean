import ParityAndBothRemainingOriginalRootDefects
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem counted_piece_order (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (C:↥K.pieces) : 11≤Nat.card C.val.supp := by
  let U := cutPieceSet G K.roots C.val
  let n := Nat.card C.val.supp
  have size : n=U.ncard := Nat.card_congr (cutPieceVertexEquiv G K.roots C.val)
  have full (x) (hx:x∈U) := uniform_tight_piece_full G 3 7 cap K.S K.T C.val C.property x hx
  have cut := actual_cut_piece_boundary_to_roots G K.S K.T K.apart C.val
  change crossCount G U Uᶜ=crossCount G U K.S+crossCount G U K.T at cut
  rw [←cut_cross_union_right G U K.S K.T K.apart] at cut
  change crossCount G U Uᶜ=K.port C at cut
  rw [K.each_has_two_ports cap none C] at cut
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  rw [degree_sum_full G U 10 full,cut,←size] at hand
  have simple := twice_edges_le_simple_order (G.induce U)
  change 2*(G.induce U).edgeSet.ncard≤U.ncard*(U.ncard-1) at simple
  rw [←size] at simple
  change 11≤n
  by_contra! small
  have bound := Nat.mul_le_mul_left n (show n-1≤9 by omega)
  have few : n≤2 := by omega
  have bound' := Nat.mul_le_mul_left n (show n-1≤1 by omega)
  omega

theorem counted_piece_quantity (cap:∀x,Nat.card (G.neighborSet x)≤10) : K.score+3≤K.pieces.ncard := by
  have root := cross_from_root_bound G 10 cap K.T K.S K.apart.symm
  have eq := K.actual
  rw [uniform_factor_cut_on_original] at eq
  change (K.pieces.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-7*(K.T.ncard:ℤ)=(K.score:ℤ) at eq
  have off := K.imbalance
  omega

theorem support_order_lower (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    11*(K.score+3)+1≤K.support.ncard := by
  classical
  let _ := Fintype.ofFinite K.pieces
  have size := Nat.card_congr (selectedCutVertexEquiv G K.roots K.pieces)
  rw [Nat.card_sigma,Nat.card_coe_set_eq] at size
  change (∑C:↥K.pieces,Nat.card C.val.supp)=K.core.ncard at size
  have add := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.pieces)) (fun C _ => K.counted_piece_order cap none C)
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at add
  rw [size] at add
  change K.pieces.ncard*11≤K.core.ncard at add
  have dis : Disjoint K.roots K.core := disjoint_compl_right.mono_right K.core_outside
  change _≤(K.roots∪K.core).ncard
  rw [Set.ncard_union_eq dis,Set.ncard_union_eq K.apart]
  have many := K.counted_piece_quantity cap
  have im := K.imbalance
  omega

#print axioms counted_piece_order
#print axioms counted_piece_quantity
#print axioms support_order_lower
end JSP452Audit.StarHost.TenOuterCut
