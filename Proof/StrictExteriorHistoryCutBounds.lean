import StrictWholeComponentHistoryPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_exterior_history_cut_bounds (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) (H:SixFiveFourHistory (F.G.induce (componentVertices F.G T)ᶜ)) :
    let d := F.rank-matchingEdges F.G
    let h := highestWidth F.n F.m F.r
    2*d≤H.fourCut.ncard ∧
      ((0<originalThresholdCount F.n 5 ∨ 0<originalThresholdCount F.m 5) → 2*d≤H.fiveCut.ncard) ∧
      ((∀i,F.n i≤4) → (∀j,F.m j≤4) → widthAt F.n F.m F.r 6≤H.fiveCut.ncard+chosenSlots F.G T 3+(h-1)) := by
  intro d h
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let P := matchingEdges (F.G.induce U)
  have closed := component_vertices_closed F.G T
  have full (v:F.X) (hv:v∈U) : Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1 :=
    ((actual (F.G.connectedComponentMk v) hv).2 v rfl).trans six.symm
  have orig := (minimal_rank_exact_source F paid).2.2.2.1
  have cap (v:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤6 :=
    (induced_neighbor_count_le F.G Uᶜ v).trans ((orig v.val).trans_eq six)
  obtain ⟨five,four⟩ := H.cut_caps cap
  obtain ⟨pr,pb,both⟩ := strict_exterior_parity_and_stages F paid U closed full
  change P+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t at pr
  change P+F.r+2*(d+∑i,(F.m i-1)/2)≤F.s at pb
  obtain ⟨i,_,_,_,_,red,_,_⟩ := strict_six_balanced_factor_cut F paid six
  have present := (original_threshold_prefix F.n F.hn 4 i).mp red.ge
  have fourth := (both H.fourCut 3 four).1 (by change 0<originalThresholdCount F.n 4;omega)
  change F.t-F.r-P-1+originalThresholdCount F.n 4≤H.fourCut.ncard at fourth
  refine ⟨by omega,?_,?_⟩
  · intro heads
    rcases heads with n|m
    · have fifth := (both H.fiveCut 4 five).1 n
      change F.t-F.r-P-1+originalThresholdCount F.n 5≤H.fiveCut.ncard at fifth
      omega
    · have fifth := (both H.fiveCut 4 five).2 m
      change F.s-F.r-P-1+originalThresholdCount F.m 5≤H.fiveCut.ncard at fifth
      omega
  · intro redSmall blueSmall
    have width := (strict_sixth_column_by_slots F paid six T).2 redSmall blueSmall
    have feas : admits_matching_remainder (O.induce H.fiveCutᶜ) 5 := by
      refine ⟨⊥,fun _ h => h.elim,?_⟩
      intro v;rw [Subgraph.spanningCoe_bot,sdiff_bot];exact five v
    have bound := (uniformEnvelope_le_deletion O 5 (by decide)).trans (deletionBudget_le_of_witness O 5 H.fiveCut feas)
    change uniformEnvelope O 6≤H.fiveCut.ncard at bound
    change widthAt F.n F.m F.r 6≤uniformEnvelope O 6+chosenSlots F.G T 3+(h-1) at width
    omega

#print axioms strict_exterior_history_cut_bounds
end JSP452Audit.StarHost
