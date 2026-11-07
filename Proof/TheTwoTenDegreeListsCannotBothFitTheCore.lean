import CompleteForestMassWhenAListFitsTheTenDegreeCore
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_double_short_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenBlockPartition F.G) (low:K.epsilon≤2)
    (excess:highestWidth F.n F.m F.r+2+K.epsilon≤K.eta)
    (left:F.s≤K.capacity) (right:F.t≤K.capacity) : False := by
  let P := K.capacity
  let k := K.outsideRank
  let a := K.roots.ncard
  let d := F.rank-matchingEdges F.G
  let h := highestWidth F.n F.m F.r
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have fee := (K.edge_fees cap).2.2.2.2
  change 2*(F.G.induce K.rest).edgeSet.ncard+10*(2*P+a+K.eta)≤2*F.G.edgeSet.ncard+K.epsilon at fee
  have edgeRank : k≤(F.G.induce K.rest).edgeSet.ncard := matchingEdges_le_edgeCount _
  have less := (minimal_rank_exact_source F paid).2.2.1
  have balance : F.rank=a+P+k+d := by have orig := K.rank;change matchingEdges F.G=a+P+k at orig;dsimp only [d];omega
  have mass := ten_short_core_mass F paid K
  have nm := mass.1 left
  have mm := mass.2 right
  change (∑i,F.n i)+d≤P+a+K.eta at nm
  change (∑i,F.m i)+d≤P+a+K.eta at mm
  have top : diagonal F.n F.m (F.r+2)=11 := by omega
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have redCap := red ⟨0,F.hs⟩
  have blueCap := blue ⟨0,F.ht⟩
  rw [ten] at redCap blueCap
  have legal := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  have profile : rowEnergy F.n F.m F.r≤F.rank+7*P+(∑i,F.n i)+(∑j,F.m j)+h := by
    by_cases order:F.s≤F.t
    · have price := shorter_head_profile_bound F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm order
        (by omega : F.r<F.s) (by decide : 3≤10) (by omega) top
      change rowEnergy F.n F.m F.r≤F.rank+7*F.t+(∑i,F.n i)+(∑j,F.m j)+h at price;change F.t≤P at right;omega
    · have peak := (diagonal_swap F.m F.n (F.r+2)).trans top
      have price := shorter_head_profile_bound F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn
        (by omega : F.t≤F.s) (by omega : F.r<F.t) (by decide : 3≤10) (by omega) peak
      rw [row_energy_colour_swap F.m F.n,highest_width_colour_swap F.m F.n,
        show rowCount F.t F.s F.r=F.rank by change F.t+F.s-1-F.r=F.s+F.t-1-F.r;omega] at price
      change rowEnergy F.n F.m F.r≤F.rank+7*F.s+(∑j,F.m j)+(∑i,F.n i)+h at price;change F.s≤P at left;omega

  have strict := F.strict
  change h+2+K.epsilon≤K.eta at excess
  omega

theorem ten_region_guard_and_long_branches (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenBlockPartition F.G) (low:K.epsilon≤2)
    (excess:highestWidth F.n F.m F.r+2+K.epsilon≤K.eta) :
    let mu := K.capacity
    let B := K.roots.ncard+mu
    let d := F.rank-matchingEdges F.G
    mu+d<max F.s F.t ∧
      ((B+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤K.outsideRank) ∨
       (F.s≤mu ∧ B+F.r+d+1≤F.t ∧ F.s≤K.outsideRank) ∨
       (F.t≤mu ∧ B+F.r+d+1≤F.s ∧ F.t≤K.outsideRank)) := by
  intro mu B d
  obtain ⟨red,blue⟩ := ten_root_list_length_dichotomy F paid K
  change F.s≤mu ∨ (F.t≤K.outsideRank ∧ mu+K.roots.ncard+F.r+d+1≤F.s) at red
  change F.t≤mu ∨ (F.s≤K.outsideRank ∧ mu+K.roots.ncard+F.r+d+1≤F.t) at blue
  have impossible := ten_double_short_impossible F paid ten K low excess
  change F.s≤mu → F.t≤mu → False at impossible
  have eqB : B=K.roots.ncard+mu := rfl
  rcases red with r|⟨rt,ls⟩
  · rcases blue with b|⟨rs,lt⟩
    · exact (impossible r b).elim
    · exact ⟨by omega,Or.inr (Or.inl ⟨r,by omega,rs⟩)⟩
  · rcases blue with b|⟨rs,lt⟩
    · exact ⟨by omega,Or.inr (Or.inr ⟨b,by omega,rt⟩)⟩
    · exact ⟨by omega,Or.inl ⟨le_min (by omega) (by omega),max_le rs rt⟩⟩

#print axioms ten_double_short_impossible
#print axioms ten_region_guard_and_long_branches
end JSP452Audit.StarHost
