import DeletePreciselyThePayableRootsAndRetainTheActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_payable_exterior_constraints (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let Y := F.G.induce P.exterior
    let Q := F.G.induce P.paidCore
    let r := F.r+P.cutRoots.ncard
    let d := F.rank-matchingEdges F.G
    P.capacity+r+d+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges Y ∧ 0<d ∧
    rowCount F.s F.t r=P.capacity+matchingEdges Y+d ∧
    ForcingRow (Q ⊕g Y) F.s F.t (padDemand F.n) (padDemand F.m) r ∧
    ForcingRow (Y ⊕g Q) F.s F.t (padDemand F.n) (padDemand F.m) r := by
  intro Y Q r d
  obtain ⟨a,b,out⟩ := P.nested_actual_sets
  have incl {S T:Set F.X} (h:S⊆T) : matchingEdges (F.G.induce S)≤matchingEdges (F.G.induce T) := by
    apply rank_le_of_copy
    exact ⟨⟨fun z => ⟨z.val,h z.property⟩,fun e => e⟩,fun _ _ eq => Subtype.ext (congrArg (fun z:↥T => z.val) eq)⟩
  have strong := (strict_only_double_escape F paid).2.2 K
  have w := Set.ncard_le_ncard a
  have z : P.capacity≤matchingEdges (F.G.induce K.core) := incl b
  have right : max F.s F.t≤matchingEdges Y := strong.2.trans (incl out)
  have deficit := (minimal_rank_exact_source F paid).2.2.1
  have rank := P.true_exterior_rank
  have pos : 0<d := by dsimp only [d];omega
  have long := strong.1
  change matchingEdges (F.G.induce K.core)+K.roots.ncard+F.r+d+1≤min F.s F.t at long
  have balance : F.rank=P.cutRoots.ncard+P.capacity+matchingEdges Y+d := by dsimp only [d,Y];omega
  obtain ⟨e⟩ := P.physical_exterior_split
  have cut := row_delete_set F.G P.cutRoots _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have row := forcingRow_of_iso e.symm cut
  refine ⟨by dsimp only [r];omega,right,pos,?_,row,forcingRow_of_iso (SimpleGraph.Iso.sumComm (G:=Q) (H:=Y)) row⟩
  change F.s+F.t-1-(F.r+P.cutRoots.ncard)=_
  change F.s+F.t-1-F.r=_ at balance
  omega

#print axioms strict_payable_exterior_constraints
end JSP452Audit.StarHost
