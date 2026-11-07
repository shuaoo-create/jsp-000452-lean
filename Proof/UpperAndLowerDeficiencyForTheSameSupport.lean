import CountsOnOneRestrictedMatching
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem restricted_matching_deficit_bound (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (targetInternal:crossCount M.spanningCoe K.T K.supportᶜ=0) :
    K.score+2+K.rootDefect K.T+crossCount G K.T K.supportᶜ+2*(K.S\M.verts).ncard≤(K.support\M.verts).ncard := by
  let R := M.spanningCoe
  let N := G \ R
  have original := actual_degree_sum_of_palette G R M.spanningCoe_le K.T
  have covered : originalDegreeSum R K.T=(K.T∩M.verts).ncard := matching_degree_sum_eq_covered M hm K.T
  change _+originalDegreeSum N K.T=_ at original
  have ledger := K.matching_token_account cap M hm
  change K.pieces.ncard+crossCount G K.T K.S+2*(R.induce K.S).edgeSet.ncard+2*(N.induce K.T).edgeSet.ncard+
    crossCount R K.S K.supportᶜ+crossCount N K.T K.supportᶜ≤(K.S∩M.verts).ncard+originalDegreeSum N K.T+(K.core∩exposedFull G M 10).ncard at ledger
  have split := cross_count_color_partition G R M.spanningCoe_le K.T K.supportᶜ
  change crossCount G K.T K.supportᶜ=crossCount R K.T K.supportᶜ+crossCount N K.T K.supportᶜ at split
  change crossCount R K.T K.supportᶜ=0 at targetInternal
  have core := K.core_uncovered cap M
  rw [←core] at ledger
  have s := split_covered_and_uncovered K.S M.verts
  have t := split_covered_and_uncovered K.T M.verts
  have missed := K.unmatched_partition M
  have capT := degree_sum_le_cap G K.T 10 (fun x _ => cap x)
  have im := K.imbalance
  have z := K.actual
  rw [uniform_factor_cut_on_original] at z
  change (K.pieces.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-7*(K.T.ncard:ℤ)=(K.score:ℤ) at z
  dsimp only [rootDefect]
  omega

theorem optimal_internal_deficit (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    let R := M.spanningCoe
    2*(R.induce K.support).edgeSet.ncard+K.score+2+K.rootDefect K.T+crossCount G K.T K.supportᶜ=K.support.ncard := by
  intro R
  let W := exposedFull G M 10
  obtain ⟨sFull,wCovered,_,zeroS,zeroT,_,_⟩ := K.matching_endpoint_saturation cap M hm attained
  have noneS : (K.S\M.verts).ncard=0 := by
    have e : K.S\M.verts=∅ := Set.eq_empty_of_forall_notMem (fun x hx => hx.2 (sFull hx.1))
    rw [e,Set.ncard_empty]
  have dis : Disjoint K.T K.core := disjoint_compl_right.mono Set.subset_union_right K.core_outside
  have all : (K.T∩W)∪(K.core∩W)=W := by
    apply Set.Subset.antisymm (Set.union_subset Set.inter_subset_right Set.inter_subset_right)
    intro x hx;exact (wCovered hx).elim (fun t => Or.inl ⟨t,hx⟩) (fun j => Or.inr ⟨j,hx⟩)
  have size := Set.ncard_union_eq (dis.mono (Set.inter_subset_left (t:=W)) (Set.inter_subset_left (t:=W)))
  rw [all] at size
  have targets := K.target_root_uncovered_count cap M hm attained
  have missed := K.unmatched_partition M
  rw [K.core_uncovered cap M,noneS,targets] at missed
  have eq := K.internal_matching_edge_deficit M hm
  change 2*(R.induce K.support).edgeSet.ncard+_+crossCount R K.S K.supportᶜ+crossCount R K.T K.supportᶜ=_ at eq
  have split := cross_count_color_partition G R M.spanningCoe_le K.T K.supportᶜ
  change crossCount R K.S K.supportᶜ=0 at zeroS
  change crossCount (G \ R) K.T K.supportᶜ=0 at zeroT
  rw [zeroT,Nat.add_zero] at split
  change W.ncard=K.score+2 at attained
  change (K.support\M.verts).ncard=0+(K.rootDefect K.T+(K.T∩W).ncard)+(K.core∩W).ncard at missed
  omega
#print axioms restricted_matching_deficit_bound
#print axioms optimal_internal_deficit
end JSP452Audit.StarHost.TenOuterCut
