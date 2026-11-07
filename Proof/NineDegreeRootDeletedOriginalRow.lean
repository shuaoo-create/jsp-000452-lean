import PhysicalSplitAfterDeletingPortRoots
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

namespace NinePortRegion
variable {X:Type u} [Finite X] {G:SimpleGraph X} (R:NinePortRegion G)
noncomputable abbrev rootDebt := rootShortfall G R.roots 9+(G.induce R.roots).edgeSet.ncard
noncomputable abbrev rankAllowance := R.roots.ncard+R.totalCapacity+R.outsideRank-matchingEdges G

theorem root_deleted_rank_allowance (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    R.rankAllowance≤R.roots.ncard ∧
    matchingEdges G+R.rankAllowance=R.roots.ncard+R.totalCapacity+R.outsideRank := by
  have rank := (R.region_rank_edges cap).2.2.1
  have cost := matching_rank_le_cut_add G R.roots
  have sub := rank_mono_embedding (SimpleGraph.Embedding.induce (G:=G) R.rootsᶜ)
  rw [rank] at cost sub
  dsimp only [rankAllowance];omega

theorem root_deleted_edge_account (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    G.edgeSet.ncard+R.rootDebt=(G.induce R.outside).edgeSet.ncard+9*(R.roots.ncard+R.totalCapacity)+8 ∧
    (R.rootDebt:ℤ)+R.K.eta≤6 := by
  have edge := (R.region_rank_edges cap).2.2.2
  have cut := root_deletion_cost_with_slack G R.roots 9 (fun x _ => cap x)
  change G.edgeSet.ncard+rootShortfall G R.roots 9+(G.induce R.roots).edgeSet.ncard=
    (G.induce R.rootsᶜ).edgeSet.ncard+9*R.roots.ncard at cut
  have fee := R.debt
  change (rootShortfall G R.roots 9:ℤ)+2*((G.induce R.roots).edgeSet.ncard:ℤ)+R.K.eta≤6 at fee
  dsimp only [rootDebt];omega

end NinePortRegion

theorem strict_nine_root_deleted_row (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) (R:NinePortRegion F.G) :
    let d := F.rank-matchingEdges F.G
    let d' := d-R.rankAllowance
    let r := F.r+R.roots.ncard
    let O := F.G.induce R.outside
    let Q := F.G.induce R.chosen
    2≤d' ∧ rowCount F.s F.t r=R.totalCapacity+R.outsideRank+d' ∧
      ForcingRow (Q⊕g O) F.s F.t (padDemand F.n) (padDemand F.m) r ∧
      ForcingRow (O⊕g Q) F.s F.t (padDemand F.n) (padDemand F.m) r := by
  intro d d' r O Q
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have gap := minimal_strict_source_deficit F paid
  dsimp only at gap;rw [nine] at gap
  have few := R.root_count.2
  change R.roots.ncard≤2 at few
  obtain ⟨hp,_,exposed,_,_⟩ := strict_nine_original_peak F paid nine
  have loss := R.root_deleted_rank_allowance cap
  have defEq : matchingEdges F.G+d=F.rank := by dsimp only [d];omega
  have lower : 2≤d' := by dsimp only [d',d];omega
  have balance : F.rank=R.roots.ncard+R.totalCapacity+R.outsideRank+d' := by dsimp only [d'] at *;omega
  have row := row_delete_set F.G R.roots _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm) (pad_positive F.n F.pn)
    (pad_positive F.m F.pm) F.row
  obtain ⟨e⟩ := R.separated_after_roots
  have physical := forcingRow_of_iso e.symm row
  refine ⟨lower,?_,physical,forcingRow_of_iso (SimpleGraph.Iso.sumComm (G:=Q) (H:=O)) physical⟩
  change F.s+F.t-1-(F.r+R.roots.ncard)=_
  change F.s+F.t-1-F.r=_ at balance
  omega

#print axioms NinePortRegion.root_deleted_rank_allowance
#print axioms NinePortRegion.root_deleted_edge_account
#print axioms strict_nine_root_deleted_row
end JSP452Audit.StarHost
