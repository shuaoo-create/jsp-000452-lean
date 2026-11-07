import TheExactTightResourceIsRealizedByOriginalEdgeSubgraphs
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X}

theorem layer_degree_on_full_set {D:ℕ} (R:SimpleGraph X) (miss A:Set X)
    (degrees:∀x,Nat.card (G.neighborSet x)=D →
      (x∈miss → Nat.card (R.neighborSet x)=0) ∧ (x∉miss → Nat.card (R.neighborSet x)=1))
    (full:∀x∈A,Nat.card (G.neighborSet x)=D) :
    originalDegreeSum R A+(A∩miss).ncard=A.ncard := by
  classical
  have point (x) (hx:x∈A.toFinite.toFinset) :
      (R.neighborSet x).ncard+(if x∈miss then 1 else 0)=1 := by
    have fee := degrees x (full x (A.toFinite.mem_toFinset.mp hx))
    by_cases inside:x∈miss
    · rw [if_pos inside];have zero := fee.1 inside;change (R.neighborSet x).ncard=0 at zero;omega
    · rw [if_neg inside];have one := fee.2 inside;change (R.neighborSet x).ncard=1 at one;omega
  have sum := Finset.sum_congr (s₁:=A.toFinite.toFinset) rfl point
  rw [Finset.sum_add_distrib,subset_indicator_sum,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at sum
  change originalDegreeSum R A+(A∩miss).ncard=A.toFinite.toFinset.card at sum
  simpa only [Set.ncard_eq_toFinset_card A A.toFinite] using sum

theorem actual_cut_piece_needs_layer_token {p q:ℕ} (odd:Odd p) (cap:∀v,Nat.card (G.neighborSet v)≤p+q)
    (S T:Set X) (apart:Disjoint S T) (C:(G.induce (S∪T)ᶜ).ConnectedComponent) (counted:C∈uniformOddPieces G p q S T)
    (R:SimpleGraph X) (sub:R≤G) (miss:Set X)
    (degrees:∀x,Nat.card (G.neighborSet x)=p+q →
      (x∈miss → Nat.card (R.neighborSet x)=0) ∧ (x∉miss → Nat.card (R.neighborSet x)=1)) :
    let U := cutPieceSet G (S∪T) C
    Odd (crossCount R U S+crossCount (G \ R) U T+(U∩miss).ncard) := by
  intro U
  have full (x) (m:x∈U) := uniform_tight_piece_full G p q cap S T C counted x m
  have total := layer_degree_on_full_set R miss U degrees full
  have hand := JSP452Audit.StarHost.two_block_handshake R U
  have boundary := palette_boundary_to_actual_roots G R sub S T apart C
  change crossCount R U Uᶜ=crossCount R U S+crossCount R U T at boundary
  rw [boundary] at hand
  have split := cross_count_color_partition G R sub U T
  have parity := uniform_member_odd_size_boundary G p q odd S T C counted
  have num : Nat.card C.supp=U.ncard := Nat.card_congr (cutPieceVertexEquiv G (S∪T) C)
  change Odd (Nat.card C.supp+crossCount G U T) at parity
  rw [num,Nat.odd_iff] at parity
  rw [Nat.odd_iff];omega

#print axioms layer_degree_on_full_set
#print axioms actual_cut_piece_needs_layer_token
end JSP452Audit.StarHost
