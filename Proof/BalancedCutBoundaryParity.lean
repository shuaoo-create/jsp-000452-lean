import ActualCutPieceBoundaries
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem cut_cross_union_right {X : Type u} [Finite X] (G : SimpleGraph X) (U S T : Set X)
    (apart : Disjoint S T) : crossCount G U (S∪T)=crossCount G U S+crossCount G U T := by
  classical
  let _ := Fintype.ofFinite U
  simp only [crossCount_eq_neighbor_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro x _
  rw [Set.inter_union_distrib_left,Set.ncard_union_eq (apart.mono Set.inter_subset_right Set.inter_subset_right)]

theorem balanced_total_boundary {X : Type u} [Finite X] (G : SimpleGraph X) (p : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤2*p) (S T : Set X) (apart : Disjoint S T) :
    crossCount G ((S∪T)ᶜ) (S∪T)+2*crossCount G T S≤2*p*S.ncard+2*p*T.ncard := by
  let O := (S∪T)ᶜ
  have so : Disjoint S O := disjoint_compl_right.mono_left Set.subset_union_left
  have to' : Disjoint T O := disjoint_compl_right.mono_left Set.subset_union_right
  have complete : S∪T∪O=Set.univ := Set.union_compl_self _
  have first := partition_handshake G S T O apart so to' complete
  have second := partition_handshake G T S O apart.symm to' so (by rw [Set.union_comm T S];exact complete)
  have boundS := degree_sum_le_cap G S (2*p) (fun x _ => cap x)
  have boundT := degree_sum_le_cap G T (2*p) (fun x _ => cap x)
  change crossCount G O (S∪T)+2*crossCount G T S≤_
  rw [cut_cross_union_right G O S T apart,crossCount_swap G O S,crossCount_swap G O T,crossCount_swap G S T] at *
  omega

theorem cut_piece_boundary_parity {X : Type u} [Finite X] (G : SimpleGraph X) (A : Set X)
    (C : (G.induce Aᶜ).ConnectedComponent) (p : ℕ)
    (full : ∀x∈cutPieceSet G A C,Nat.card (G.neighborSet x)=2*p) :
    2∣crossCount G (cutPieceSet G A C) A := by
  classical
  let U := cutPieceSet G A C
  let _ := Fintype.ofFinite U
  have incid : crossCount G U Uᶜ=crossCount G U A := by
    simp only [crossCount_eq_neighbor_sum]
    apply Finset.sum_congr rfl;intro x _
    congr 1
    ext y
    constructor
    · rintro ⟨adj,out⟩
      refine ⟨adj,?_⟩
      by_contra away;exact out (cut_piece_neighbor G A C x.property adj away)
    · rintro ⟨adj,ina⟩
      exact ⟨adj,fun inU => (cut_piece_outside G A C inU) ina⟩
  have degree := degree_sum_full G U (2*p) full
  have budget := JSP452Audit.StarHost.two_block_handshake G U
  rw [incid,degree] at budget
  rw [Nat.mul_assoc] at budget
  change 2∣crossCount G U A
  omega

#print axioms cut_cross_union_right
#print axioms balanced_total_boundary
#print axioms cut_piece_boundary_parity
end JSP452Audit.StarHost