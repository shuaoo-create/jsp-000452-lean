import TwoUnselectedMembersOfTheOriginalNineCut
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

namespace NineOriginalCut
variable {X : Type u} [Finite X] {G : SimpleGraph X} (K : NineOriginalCut G)

theorem different_cut_labels_disjoint {c d : ↥K.blocks} (ne : c≠d) :
    Disjoint (K.labels c) (K.labels d) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨v,hv,rfl⟩ ⟨w,hw,eq⟩
  have same : w=v := Subtype.ext eq
  subst w
  have label := (show (G.induce K.barrierᶜ).connectedComponentMk v=c.val from hv).symm.trans hw
  exact ne (Subtype.ext label)

theorem positive_cut_card (c : ↥K.blocks) : 0<(K.labels c).ncard := by
  obtain ⟨v,inside⟩ := c.val.nonempty_supp
  exact (Set.ncard_pos (K.labels c).toFinite).mpr ⟨v.val,v,inside,rfl⟩

theorem inexpensive_cut_member_order (cap : ∀v,Nat.card (G.neighborSet v)≤9) (c : ↥K.blocks)
    (fee : K.sPorts c+K.tPorts c≤8) : 10≤(K.labels c).ncard := by
  let U := K.labels c
  let n := U.ncard
  have full (x) (hx : x∈U) := uniform_tight_piece_full G 3 6 cap K.S K.T c.val c.property x hx
  have boundary := actual_cut_piece_boundary_to_roots G K.S K.T K.apart c.val
  change crossCount G U Uᶜ=K.sPorts c+K.tPorts c at boundary
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  rw [degree_sum_full G U 9 full,boundary] at hand
  change 9*n=2*(G.induce U).edgeSet.ncard+(K.sPorts c+K.tPorts c) at hand
  have simple := twice_edges_le_simple_order (G.induce U)
  change 2*(G.induce U).edgeSet.ncard≤n*(n-1) at simple
  have positive : 0<n := K.positive_cut_card c
  change 10≤n
  by_contra! small
  have upper := Nat.mul_le_mul_right (n-1) (show n≤9 by omega)
  omega

end NineOriginalCut
namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem spare_member_keeps_full_degree (cap : ∀v,Nat.card (G.neighborSet v)≤9) (c : ↥R.K.blocks)
    (zero : c≠(R.select 0).val) (one : c≠(R.select 1).val) {x : X} (inside : x∈R.K.labels c) :
    Nat.card (R.erased.neighborSet x)=9 := by
  have away : x∉R.chosen := fun h => h.elim (fun z => Set.disjoint_left.mp (R.K.different_cut_labels_disjoint zero) inside z)
    (fun z => Set.disjoint_left.mp (R.K.different_cut_labels_disjoint one) inside z)
  have root : x∉R.K.barrier := cut_piece_outside G R.K.barrier c.val inside
  have edges : R.erased.neighborSet x=G.neighborSet x := by
    ext y
    constructor
    · exact fun h => h.1
    · intro adj
      refine ⟨adj,fun marked => ?_⟩
      have side (i : Fin 2) (inc : R.box i⊆R.chosen) (hit : (R.portPart i).Adj x y) : False := by
        rcases (R.portPart_edges i x y).mp hit with inner|⟨_,ends⟩
        · exact away (inc ((portInside_adj G (R.box i) x y).mp inner).2.1)
        · rcases ends with ⟨xt,_⟩|⟨_,xr⟩
          · exact away (inc (xt.symm ▸ (R.port i).tip_mem))
          · exact root (Or.inl (xr.symm ▸ (R.port i).root_mem))
      exact marked.elim (side 0 Set.subset_union_left) (side 1 Set.subset_union_right)
  rw [edges]
  exact uniform_tight_piece_full G 3 6 cap R.K.S R.K.T c.val c.property x inside

theorem eleven_spare_full_vertices (cap : ∀v,Nat.card (G.neighborSet v)≤9) :
    ∃U : Set X,11≤U.ncard ∧ ∀x∈U,Nat.card (R.erased.neighborSet x)=9 := by
  obtain ⟨c,d,c0,c1,d0,d1,ne,fee⟩ := R.two_other_cut_members cap
  have many := R.K.inexpensive_cut_member_order cap c fee
  have one := R.K.positive_cut_card d
  have size := Set.ncard_union_eq (R.K.different_cut_labels_disjoint ne)
  exact ⟨R.K.labels c∪R.K.labels d,by omega,fun x h => h.elim (R.spare_member_keeps_full_degree cap c c0 c1)
    (R.spare_member_keeps_full_degree cap d d0 d1)⟩

#print axioms spare_member_keeps_full_degree
#print axioms eleven_spare_full_vertices
end NinePortRegion
#print axioms NineOriginalCut.different_cut_labels_disjoint
#print axioms NineOriginalCut.positive_cut_card
#print axioms NineOriginalCut.inexpensive_cut_member_order
end JSP452Audit.StarHost
