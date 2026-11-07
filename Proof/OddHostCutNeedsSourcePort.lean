import NineDegreeOriginalExposureLimit
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem actual_cut_piece_boundary_to_roots {X:Type u} [Finite X] (G:SimpleGraph X) (S T:Set X)
    (dis:Disjoint S T) (C:(G.induce (S∪T)ᶜ).ConnectedComponent) :
    let U := cutPieceSet G (S∪T) C
    crossCount G U Uᶜ=crossCount G U S+crossCount G U T := by
  classical
  intro U
  let A := S∪T
  let _ := Fintype.ofFinite U
  have eq : crossCount G U Uᶜ=crossCount G U A := by
    simp only [crossCount_eq_neighbor_sum]
    apply Finset.sum_congr rfl
    intro x _
    congr 1;ext y
    constructor
    · rintro ⟨adj,out⟩
      refine ⟨adj,?_⟩
      by_contra away;exact out (cut_piece_neighbor G A C x.property adj away)
    · rintro ⟨adj,inA⟩;exact ⟨adj,fun u => cut_piece_outside G A C u inA⟩
  exact eq.trans (cut_cross_union_right G U S T dis)

theorem counted_piece_has_odd_source_ports {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ)
    (odd:Odd (a+b)) (oddA:Odd a) (cap:∀x,Nat.card (G.neighborSet x)≤a+b)
    (S T:Set X) (dis:Disjoint S T) (C:(G.induce (S∪T)ᶜ).ConnectedComponent)
    (mem:C∈uniformOddPieces G a b S T) : Odd (crossCount G (cutPieceSet G (S∪T) C) S) := by
  let U := cutPieceSet G (S∪T) C
  have full (x) (hx:x∈U) := uniform_tight_piece_full G a b cap S T C mem x hx
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  rw [degree_sum_full G U (a+b) full,actual_cut_piece_boundary_to_roots G S T dis C] at hand
  have size : Nat.card C.supp=U.ncard := Nat.card_congr (cutPieceVertexEquiv G (S∪T) C)
  have shape := uniform_member_odd_size_boundary G a b oddA S T C mem
  change Odd (Nat.card C.supp+crossCount G U T) at shape
  rw [size,Nat.odd_iff,Nat.add_mod] at shape
  have modEq := congrArg (fun v:ℕ => v%2) hand
  change ((a+b)*U.ncard)%2=(2*(G.induce U).edgeSet.ncard+(crossCount G U S+crossCount G U T))%2 at modEq
  rw [Nat.mul_mod,Nat.odd_iff.mp odd,Nat.one_mul,Nat.mod_mod] at modEq
  rw [Nat.odd_iff];change crossCount G U S%2=1
  omega

theorem cross_from_root_bound {X:Type u} [Finite X] (G:SimpleGraph X) (D:ℕ) (cap:∀x,Nat.card (G.neighborSet x)≤D)
    (S V:Set X) (outside:Disjoint S V) :
    crossCount G S V≤D*S.ncard := by
  classical
  let _ := Fintype.ofFinite S
  have sum := Finset.sum_le_sum (s:=(Finset.univ:Finset S)) (fun x _ =>
    (Set.ncard_le_ncard (Set.inter_subset_left (s:=G.neighborSet x.val) (t:=V))).trans (cap x.val))
  rw [←crossCount_eq_neighbor_sum,Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id] at sum
  change crossCount G S V≤S.ncard*D at sum;simpa only [Nat.mul_comm D] using sum

#print axioms actual_cut_piece_boundary_to_roots
#print axioms counted_piece_has_odd_source_ports
#print axioms cross_from_root_bound
end JSP452Audit.StarHost
