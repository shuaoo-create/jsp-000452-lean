import ActualMatchingAndComplementCrossings
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem selected_color_cross_sum {X:Type u} [Finite X] (G R:SimpleGraph X) (A:Set X)
    (B:Set (G.induce Aᶜ).ConnectedComponent) [Fintype B] (T:Set X) :
    crossCount R (regionCore G A B) T=∑C:↥B,crossCount R (cutPieceSet G A C.val) T := by
  classical
  let _ := Fintype.ofFinite ↥(regionCore G A B)
  let _ (C:↥B) := Fintype.ofFinite ↥C.val.supp
  let f (v:X) := (R.neighborSet v∩T).ncard
  have single (C:↥B) : crossCount R (cutPieceSet G A C.val) T=∑x:C.val.supp,f x.val.val := by
    let _ := Fintype.ofFinite ↥(cutPieceSet G A C.val)
    rw [crossCount_eq_neighbor_sum]
    exact (Fintype.sum_equiv (cutPieceVertexEquiv G A C.val) (fun x:C.val.supp => f x.val.val)
      (fun y:↥(cutPieceSet G A C.val) => f y.val) (fun _ => rfl)).symm
  simp_rw [single]
  rw [crossCount_eq_neighbor_sum]
  have eq := Fintype.sum_equiv (selectedCutVertexEquiv G A B) (fun x:((C:↥B) × C.val.supp) => f x.2.val.val)
    (fun y:↥(regionCore G A B) => f y.val) (fun _ => rfl)
  rw [Fintype.sum_sigma] at eq
  exact eq.symm

theorem selected_piece_intersections {X:Type u} [Finite X] (G:SimpleGraph X) (A:Set X)
    (B:Set (G.induce Aᶜ).ConnectedComponent) [Fintype B] (W:Set X) :
    (regionCore G A B∩W).ncard=∑c:↥B,(cutPieceSet G A c.val∩W).ncard := by
  classical
  let L (c:↥B) := cutPieceSet G A c.val∩W
  have union : regionCore G A B∩W=⋃c:↥B,L c := by
    ext x
    constructor
    · rintro ⟨⟨v,rfl,mem⟩,inW⟩
      exact Set.mem_iUnion.mpr ⟨⟨(G.induce Aᶜ).connectedComponentMk v,mem⟩,⟨v,rfl,rfl⟩,inW⟩
    · intro h
      obtain ⟨c,⟨v,hv,rfl⟩,inW⟩ := Set.mem_iUnion.mp h
      exact ⟨⟨v,rfl,(show (G.induce Aᶜ).connectedComponentMk v=c.val from hv).symm ▸ c.property⟩,inW⟩
  have dis : Pairwise (Function.onFun Disjoint L) := by
    intro c d ne
    apply Set.disjoint_left.mpr
    rintro _ ⟨⟨v,hv,rfl⟩,_⟩ ⟨⟨w,hw,eq⟩,_⟩
    have same : w=v := Subtype.ext eq
    subst w
    exact ne (Subtype.ext ((show (G.induce Aᶜ).connectedComponentMk v=c.val from hv).symm.trans hw))
  rw [union,Set.ncard_iUnion_of_finite (fun c => Set.toFinite (L c)) dis,finsum_eq_sum_of_fintype]

namespace NineOriginalCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)
noncomputable def matchingUse (M:G.Subgraph) (c:↥K.blocks) : ℕ :=
  crossCount M.spanningCoe (K.labels c) K.S+crossCount (G \ M.spanningCoe) (K.labels c) K.T+
    (K.labels c∩exposedFull G M 9).ncard

theorem matching_use_local (cap:∀x,Nat.card (G.neighborSet x)≤9) (M:G.Subgraph) (hm:M.IsMatching) (c:↥K.blocks) :
    Odd (K.matchingUse M c) ∧
      2*(M.spanningCoe.induce (K.labels c)).edgeSet.ncard+K.matchingUse M c=
        (K.labels c).ncard+K.tPorts c-2*crossCount M.spanningCoe (K.labels c) K.T := by
  let U := K.labels c
  let R := M.spanningCoe
  have full (x) (hx:x∈U) := uniform_tight_piece_full G 3 6 cap K.S K.T c.val c.property x hx
  have cover := matching_degree_sum_and_missed_labels M hm U 9 full
  have hand := JSP452Audit.StarHost.two_block_handshake R U
  have boundary := palette_boundary_to_actual_roots G R M.spanningCoe_le K.S K.T K.apart c.val
  change crossCount R U Uᶜ=crossCount R U K.S+crossCount R U K.T at boundary
  rw [boundary] at hand
  have color := cross_count_color_partition G R M.spanningCoe_le U K.T
  have odd := uniform_member_odd_size_boundary G 3 6 (by decide) K.S K.T c.val c.property
  have size : Nat.card c.val.supp=U.ncard := Nat.card_congr (cutPieceVertexEquiv G K.barrier c.val)
  change Odd (Nat.card c.val.supp+crossCount G U K.T) at odd
  rw [size] at odd
  change originalDegreeSum R U+(U∩exposedFull G M 9).ncard=U.ncard at cover
  have value : K.matchingUse M c=crossCount R U K.S+crossCount (G \ R) U K.T+(U∩exposedFull G M 9).ncard := rfl
  have eq : 2*(R.induce U).edgeSet.ncard+K.matchingUse M c+2*crossCount R U K.T=U.ncard+crossCount G U K.T := by omega
  refine ⟨?_,?_⟩
  · rw [Nat.odd_iff] at odd ⊢;omega
  · change 2*(R.induce U).edgeSet.ncard+K.matchingUse M c=U.ncard+crossCount G U K.T-2*crossCount R U K.T
    omega
#print axioms matching_use_local
end NineOriginalCut
#print axioms selected_color_cross_sum
#print axioms selected_piece_intersections
end JSP452Audit.StarHost
