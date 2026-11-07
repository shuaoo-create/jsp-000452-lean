import QuarticTernaryActualPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Every quartic minimal source would have to contain a full head;
its opposite must be three, whose actual remaining cases are now paid. -/
theorem strict_source_degree_at_least_five (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    5≤diagonal F.n F.m (F.r+2)-1 := by
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  have least : 4≤D := strict_source_degree_at_least_four F paid
  by_contra! small
  have four : D=4 := by omega
  obtain ⟨K⟩ := degreeRegion_exists F.G D
  let μ := matchingEdges (F.G.induce K.core)
  let a := K.roots.ncard
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  have root := ((low_degree_original_costs F paid K).2.1 four).2
  have cost : 4*minimumExposure F.G D+rootShortfall F.G K.roots D≤2*highestWidth F.n F.m F.r+10 := by
    change 4*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤2*highestWidth F.n F.m F.r+10 at root;omega
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have outer := strict_exterior_endpoint_guards F paid K
  have mass := strict_source_whole_list_alternatives F K
  have data := strict_both_complete_exteriors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have binary := strict_quartic_opposite_must_be_three F paid K four
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have bad := F.strict
  by_cases red : F.n ⟨0,F.hs⟩=D
  · obtain ⟨embedded,len,_,_⟩ := unique.1 red
    change μ+a+F.r+d+1≤F.s at len
    have escaped : μ<F.s := by omega
    change F.t≤μ at embedded
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;omega)).1
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    have ext := outer.1 escaped
    change a+F.r+2*(d+_)+_≤F.s-μ at ext
    have fee := quartic_full_ternary_paid F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm four cap F.live red
      (binary.1 (red.trans four)) top d rank (data.1 escaped) escaped (by change F.t+d≤μ+1;omega)
      guards.1 (by change a+F.r+2*d≤F.s-μ;omega) width res cost (trigger.1 red)
    omega
  · have blue : F.m ⟨0,F.ht⟩=D := by
      by_contra no
      have n := nc ⟨0,F.hs⟩;have m := mc ⟨0,F.ht⟩
      have large := minimal_subcap_heads_force_degree_six F paid (by omega) (by omega)
      omega
    obtain ⟨embedded,len,_,_⟩ := unique.2 blue
    change μ+a+F.r+d+1≤F.t at len
    have escaped : μ<F.t := by omega
    change F.s≤μ at embedded
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;omega)).1
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    have ext := outer.2 escaped
    change a+F.r+2*(d+_)+_≤F.t-μ at ext
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have H := highest_width_colour_swap F.m F.n F.r
    have fee := quartic_full_ternary_paid F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn four cap (by rw [swap];exact F.live) blue
      (binary.2 (blue.trans four)) ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm) (by rw [swap];exact data.2 escaped)
      escaped (by change F.s+d≤μ+1;omega) guards.2 (by change a+F.r+2*d≤F.t-μ;omega)
      (by rw [H];exact width) res (by rw [H];exact cost) (trigger.2 blue)
    rw [row_energy_colour_swap F.m F.n] at fee;omega

theorem original_failure_needs_degree_five {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 5≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ RemainingOriginalRegimes F := by
  obtain ⟨F,paid,_,edges,order,types⟩ := original_failure_two_remaining_regimes.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_five F paid,edges,order,types⟩

#print axioms strict_source_degree_at_least_five
#print axioms original_failure_needs_degree_five
end JSP452Audit.StarHost
