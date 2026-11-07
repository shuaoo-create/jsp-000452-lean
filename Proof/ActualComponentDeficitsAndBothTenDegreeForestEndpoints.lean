import TenDegreeDeficitAfterPayingEightLowerColumns
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem TenRegularBudget.exposed_in_original {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenRegularBudget G) :
    2*K.slack+K.eps≤minimumExposure G 10 := by
  obtain ⟨M,hm,_,opt⟩ := minimumExposure_attained G 10
  let R := M.spanningCoe
  have cross : crossCount R K.support K.supportᶜ=0 := crossCount_of_no_edges R _ _
    (fun x h y out edge => out (K.support_closed x h y (M.adj_sub edge)))
  have hand := JSP452Audit.StarHost.two_block_handshake R K.support
  have cost := matching_degree_sum_and_missed_labels M hm K.support 10 K.support_full
  change originalDegreeSum R K.support+(K.support∩exposedFull G M 10).ncard=K.support.ncard at cost
  have bound := Set.ncard_le_ncard (Set.inter_subset_right (s:=K.support) (t:=exposedFull G M 10))
  have rank := edges_of_matching_inside_set M hm K.support
  change (R.induce K.support).edgeSet.ncard≤_ at rank
  have size : K.support.ncard=2*K.P+K.eps := K.order
  have fit : matchingEdges (G.induce K.support)≤K.P := K.fits
  dsimp only [TenRegularBudget.slack];omega

theorem ten_conservative_forest_endpoints (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) :
    let d := F.rank-matchingEdges F.G
    let J := K.slack
    let ds := d-J
    let q := F.t-F.r-K.P
    let k := F.s-F.r-K.P
    let O := F.G.induce K.supportᶜ
    J+K.eps+1≤ds ∧ matchingEdges O+K.P+ds=F.rank ∧
    2*(ds+∑i,(F.n i-1)/2)+J≤q ∧ 2*(ds+∑j,(F.m j-1)/2)+J≤k ∧
    ForestMatchingEndpoint O F.n q ∧ ForestMatchingEndpoint O F.m k := by
  intro d J ds q k O
  let P := matchingEdges (F.G.induce K.support)
  have full (x) (hx:x∈K.support) := (K.support_full x hx).trans ten.symm
  obtain ⟨len,_⟩ := strict_closed_union_lengths F paid K.support K.support_closed full
  obtain ⟨qa,ka,op,ok,left,right⟩ := strict_closed_union_endpoint_pair F paid K.support K.support_closed full
  change P+F.r+d+1≤min F.s F.t at len
  change d+1≤F.t-F.r-P at qa
  change d+1≤F.s-F.r-P at ka
  change matchingEdges O+d+1=F.s+(F.t-F.r-P) at op
  change matchingEdges O+d+1=F.t+(F.s-F.r-P) at ok
  change ForestMatchingEndpoint O F.n (F.t-F.r-P) at left
  change ForestMatchingEndpoint O F.m (F.s-F.r-P) at right
  have split := closed_union_matching_split F.G K.support K.support_closed
  change matchingEdges F.G=P+matchingEdges O at split
  have gap := minimal_strict_source_deficit F paid
  dsimp only at gap;rw [ten] at gap
  have deep : minimumExposure F.G 10+1≤d := gap.2.1
  have un := K.exposed_in_original
  change 2*J+K.eps≤minimumExposure F.G 10 at un
  have fit : P≤K.P := K.fits
  have jEq : J=K.P-P := rfl
  have lower : matchingEdges F.G+d=F.rank := by
    have small := (minimal_rank_exact_source F paid).2.2.1
    dsimp only [d];omega
  have lenS := len.trans (Nat.min_le_left _ _)
  have lenT := len.trans (Nat.min_le_right _ _)
  have v := endpoint_forest_parity_cost O F.n F.pn left (by omega) (by omega) (by omega) op
  have w := endpoint_forest_parity_cost O F.m F.pm right (by omega) (by omega) (by omega) ok
  refine ⟨by dsimp only [ds];omega,by dsimp only [ds];omega,by dsimp only [ds,q];omega,by dsimp only [ds,k];omega,?_,?_⟩
  · intro R sub
    rcases left R sub with forest|mat
    · exact Or.inl forest
    · exact Or.inr (by dsimp only [q];omega)
  · intro R sub
    rcases right R sub with forest|mat
    · exact Or.inl forest
    · exact Or.inr (by dsimp only [k];omega)

theorem ten_regular_unconditional_volume (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) :
    K.P+14*K.eps+6+3*K.slack≤3*(F.rank-matchingEdges F.G)+6*highestWidth F.n F.m F.r := by
  obtain ⟨n,m,_⟩ := strict_only_double_escape F paid
  have a (i) : F.n i+2≤11 := by have h := n i;rw [ten] at h;omega
  have b (i) : F.m i+2≤11 := by have h := m i;rw [ten] at h;omega
  have budget := ten_regular_exterior_slot_deficit F paid ten K 2 a b
  have slots := ten_regular_slot_volume K 2
  omega

#print axioms TenRegularBudget.exposed_in_original
#print axioms ten_conservative_forest_endpoints
#print axioms ten_regular_unconditional_volume
end JSP452Audit.StarHost
