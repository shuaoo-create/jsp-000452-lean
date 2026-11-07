import ShortBoxForestMassAndOrder
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_double_short_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) (R:NinePortRegion F.G)
    (left:F.s≤R.totalCapacity) (right:F.t≤R.totalCapacity) : False := by
  let P := R.totalCapacity
  let k := R.outsideRank
  let a := R.roots.ncard
  let d := F.rank-matchingEdges F.G-R.rankAllowance
  let h := highestWidth F.n F.m F.r
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have debt := R.root_deleted_edge_account cap
  have xi : R.rootDebt≤5 := by have := R.exposure;omega
  change F.G.edgeSet.ncard+R.rootDebt=(F.G.induce R.outside).edgeSet.ncard+9*(a+P)+8 ∧ _ at debt
  have edgeRank : k≤(F.G.induce R.outside).edgeSet.ncard := matchingEdges_le_edgeCount _
  have dpos := (strict_nine_root_deleted_row F paid nine R).1
  change 2≤d at dpos
  have tally := (strict_nine_root_deleted_row F paid nine R).2.1
  change F.s+F.t-1-(F.r+a)=P+k+d at tally
  have nf : F.rank=a+P+k+d := by change F.s+F.t-1-F.r=_;omega
  have mass := strict_nine_short_box_masses F paid nine R
  have nm := mass.1 left
  have mm := mass.2 right
  change (∑i,F.n i)+d≤P+2 at nm
  change (∑i,F.m i)+d≤P+2 at mm
  have top : diagonal F.n F.m (F.r+2)=10 := by omega
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have redCap := red ⟨0,F.hs⟩
  have blueCap := blue ⟨0,F.ht⟩
  rw [nine] at redCap blueCap
  have legal := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  have profile : rowEnergy F.n F.m F.r≤F.rank+6*P+(∑i,F.n i)+(∑j,F.m j)+h := by
    by_cases order:F.s≤F.t
    · have price := shorter_head_profile_bound F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm order
        (by omega : F.r<F.s) (by decide : 3≤9) (by omega) top
      change rowEnergy F.n F.m F.r≤F.rank+6*F.t+(∑i,F.n i)+(∑j,F.m j)+h at price;change F.t≤P at right;omega
    · have peak := (diagonal_swap F.m F.n (F.r+2)).trans top
      have price := shorter_head_profile_bound F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn
        (by omega : F.t≤F.s) (by omega : F.r<F.t) (by decide : 3≤9) (by omega) peak
      rw [row_energy_colour_swap F.m F.n,highest_width_colour_swap F.m F.n,
        show rowCount F.t F.s F.r=F.rank by change F.t+F.s-1-F.r=F.s+F.t-1-F.r;omega] at price
      change rowEnergy F.n F.m F.r≤F.rank+6*F.s+(∑j,F.m j)+(∑i,F.n i)+h at price;change F.s≤P at left;omega
  have strict := F.strict
  have root : 1≤a := R.root_count.1
  have up : h≤2 := (strict_nine_original_peak F paid nine).2.1
  omega

theorem strict_nine_one_long_list (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) (R:NinePortRegion F.G) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    P+(F.r+R.roots.ncard)+d+1≤max F.s F.t := by
  intro P d
  obtain ⟨red,blue⟩ := nine_port_pair_length_gap F paid nine R
  by_contra! no
  have s : F.s≤P := red.resolve_right (by omega)
  have t : F.t≤P := blue.resolve_right (by omega)
  exact strict_nine_double_short_impossible F paid nine R s t

#print axioms strict_nine_double_short_impossible
#print axioms strict_nine_one_long_list
end JSP452Audit.StarHost
