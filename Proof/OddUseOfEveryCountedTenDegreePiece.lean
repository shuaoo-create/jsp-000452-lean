import SizeAndEdgeCountOnTheIdenticalTenDegreeSupport
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

abbrev labels (c:↥K.pieces) := cutPieceSet G K.roots c.val
noncomputable def matchingUse (M:G.Subgraph) (c:↥K.pieces) : ℕ :=
  crossCount M.spanningCoe (K.labels c) K.S+crossCount (G \ M.spanningCoe) (K.labels c) K.T+
    (K.labels c∩exposedFull G M 10).ncard

theorem matching_use_local (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching) (c:↥K.pieces) :
    Odd (K.matchingUse M c) ∧
      2*(M.spanningCoe.induce (K.labels c)).edgeSet.ncard+K.matchingUse M c=
        (K.labels c).ncard+crossCount G (K.labels c) K.T-2*crossCount M.spanningCoe (K.labels c) K.T := by
  let U := K.labels c
  let R := M.spanningCoe
  have full (x) (hx:x∈U) := uniform_tight_piece_full G 3 7 cap K.S K.T c.val c.property x hx
  have cover := matching_degree_sum_and_missed_labels M hm U 10 full
  have hand := JSP452Audit.StarHost.two_block_handshake R U
  have boundary := palette_boundary_to_actual_roots G R M.spanningCoe_le K.S K.T K.apart c.val
  change crossCount R U Uᶜ=crossCount R U K.S+crossCount R U K.T at boundary
  rw [boundary] at hand
  have color := cross_count_color_partition G R M.spanningCoe_le U K.T
  have odd := uniform_member_odd_size_boundary G 3 7 (by decide) K.S K.T c.val c.property
  have size : Nat.card c.val.supp=U.ncard := Nat.card_congr (cutPieceVertexEquiv G K.roots c.val)
  change Odd (Nat.card c.val.supp+crossCount G U K.T) at odd
  rw [size] at odd
  change originalDegreeSum R U+(U∩exposedFull G M 10).ncard=U.ncard at cover
  have value : K.matchingUse M c=crossCount R U K.S+crossCount (G \ R) U K.T+(U∩exposedFull G M 10).ncard := rfl
  have eq : 2*(R.induce U).edgeSet.ncard+K.matchingUse M c+2*crossCount R U K.T=U.ncard+crossCount G U K.T := by omega
  refine ⟨?_,?_⟩
  · rw [Nat.odd_iff] at odd ⊢;omega
  · change 2*(R.induce U).edgeSet.ncard+K.matchingUse M c=U.ncard+crossCount G U K.T-2*crossCount R U K.T
    omega


theorem aggregate_piece_tokens (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching) :
    let R := M.spanningCoe
    let N := G \ R
    K.pieces.ncard≤crossCount R K.core K.S+crossCount N K.core K.T+
      (K.core∩exposedFull G M 10).ncard := by
  classical
  intro R N
  let _ := Fintype.ofFinite K.pieces
  have each (c:↥K.pieces) : 1≤K.matchingUse M c := by obtain ⟨k,eq⟩ := (K.matching_use_local cap M hm c).1;omega
  have pos := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.pieces)) (fun c _ => each c)
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at pos
  change K.pieces.ncard≤∑c:↥K.pieces,(crossCount R (K.labels c) K.S+crossCount N (K.labels c) K.T+
    (K.labels c∩exposedFull G M 10).ncard) at pos
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at pos
  have red := selected_color_cross_sum G R K.roots K.pieces K.S
  have blue := selected_color_cross_sum G N K.roots K.pieces K.T
  have uncovered := selected_piece_intersections G K.roots K.pieces (exposedFull G M 10)
  change crossCount R K.core K.S=∑c:↥K.pieces,crossCount R (K.labels c) K.S at red
  change crossCount N K.core K.T=∑c:↥K.pieces,crossCount N (K.labels c) K.T at blue
  change (K.core∩exposedFull G M 10).ncard=∑c:↥K.pieces,(K.labels c∩exposedFull G M 10).ncard at uncovered
  rwa [←red,←blue,←uncovered] at pos

#print axioms matching_use_local
#print axioms aggregate_piece_tokens
end JSP452Audit.StarHost.TenOuterCut
