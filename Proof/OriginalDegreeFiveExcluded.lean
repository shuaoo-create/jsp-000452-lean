import QuinticRetainedActualPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_source_degree_at_least_six (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    6≤diagonal F.n F.m (F.r+2)-1 := by
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  have least : 5≤D := strict_source_degree_at_least_five F paid
  by_contra! small
  have five : D=5 := by omega
  obtain ⟨K⟩ := degreeRegion_exists F.G D
  let a := K.roots.ncard
  let μ := matchingEdges (F.G.induce K.core)
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  have root := ((low_degree_original_costs F paid K).2.2 five).2.1
  have cost : 3*minimumExposure F.G D+rootShortfall F.G K.roots D≤10 := by
    change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤10 at root;omega
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have mass := strict_source_whole_list_alternatives F K
  have data := strict_both_complete_exteriors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have retained := strict_quintic_exterior_nonunit F paid five K
  have bad := F.strict
  rcases (strict_quintic_heads_and_positive_offset F paid five).2 with ⟨red,h⟩|⟨blue,h⟩
  · have full := red.trans five.symm
    obtain ⟨embedded,len,_,_⟩ := unique.1 full
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by omega
    change F.t≤μ at embedded
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;omega)).1
    have fee := quintic_full_retained_paid F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm five cap F.live F.row full h
      top d rank (data.1 esc) esc guards.1 half width res cost (trigger.1 full) (retained.1 red)
    omega
  · have full := blue.trans five.symm
    obtain ⟨embedded,len,_,_⟩ := unique.2 full
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by omega
    change F.s≤μ at embedded
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;omega)).1
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have H := highest_width_colour_swap F.m F.n F.r
    have fee := quintic_full_retained_paid F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn five cap (by rw [swap];exact F.live)
      (swap_positive_forcing_row F.G _ _ F.row) full h ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm)
      (by rw [swap];exact data.2 esc) esc guards.2 half (by rw [H];exact width) res cost (trigger.2 full) (retained.2 blue)
    rw [row_energy_colour_swap F.m F.n] at fee;omega

theorem original_failure_needs_degree_six {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 6≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ RemainingOriginalRegimes F := by
  obtain ⟨F,paid,_,edges,order,types⟩ := original_failure_needs_degree_five.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_six F paid,edges,order,types⟩

#print axioms strict_source_degree_at_least_six
#print axioms original_failure_needs_degree_six
end JSP452Audit.StarHost