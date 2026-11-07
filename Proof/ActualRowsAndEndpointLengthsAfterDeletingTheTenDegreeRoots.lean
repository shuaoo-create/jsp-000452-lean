import ExactDeletionsOnTheCommonTenDegreePartition
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_physical_root_deleted_row (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (K:TenBlockPartition F.G) :
    let d := F.rank-matchingEdges F.G
    let r := F.r+K.roots.ncard
    let O := F.G.induce K.rest
    let Q := F.G.induce K.core
    2≤d ∧ rowCount F.s F.t r=K.capacity+K.outsideRank+d ∧
      ForcingRow (Q⊕g O) F.s F.t (padDemand F.n) (padDemand F.m) r ∧
      ForcingRow (O⊕g Q) F.s F.t (padDemand F.n) (padDemand F.m) r := by
  intro d r O Q
  have deep := (minimal_strict_source_deficit F paid).2.2
  change 2≤d at deep
  have strict := (minimal_rank_exact_source F paid).2.2.1
  have size : matchingEdges F.G+d=F.rank := by dsimp only [d];omega
  rw [K.rank] at size
  have row := row_delete_set F.G K.roots _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have actual := forcingRow_of_iso K.after_roots_iso.symm row
  refine ⟨deep,?_,actual,forcingRow_of_iso (SimpleGraph.Iso.sumComm (G:=Q) (H:=O)) actual⟩
  change rowCount F.s F.t (F.r+K.roots.ncard)=_
  change K.roots.ncard+K.capacity+K.outsideRank+d=F.s+F.t-1-F.r at size
  dsimp only [rowCount];omega

theorem ten_common_endpoint_guards (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (K:TenBlockPartition F.G) :
    let d := F.rank-matchingEdges F.G
    K.roots.ncard+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t ∧
    K.roots.ncard+F.r+2*(d+∑i,(F.m i-1)/2)≤F.s := by
  intro d
  have bounds := (minimal_rank_exact_source F paid).2.2.1
  have pos : 0<d := by dsimp only [d];omega
  have sum : matchingEdges F.G+d=F.rank := by dsimp only [d];omega
  have split := (rank_eq_of_graph_iso K.after_roots_iso).symm
  rw [matchingEdges_sumGraph] at split
  have goalRank : matchingEdges F.G=K.roots.ncard+matchingEdges (F.G.induce K.rootsᶜ) := by rw [split,K.rank];omega
  obtain ⟨B,tight,large,critical⟩ := tight_cut_size_after_exact_rank_loss F.G K.roots goalRank
  have fees := full_row_endpoint_guards F.G F.hs F.ht F.n F.m F.pn F.pm F.row B tight (fun c => (critical c).2) d pos sum
  omega

theorem ten_root_list_length_dichotomy (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (K:TenBlockPartition F.G) :
    let d := F.rank-matchingEdges F.G
    let a := K.roots.ncard
    (F.s≤K.capacity ∨ (F.t≤K.outsideRank ∧ K.capacity+a+F.r+d+1≤F.s)) ∧
    (F.t≤K.capacity ∨ (F.s≤K.outsideRank ∧ K.capacity+a+F.r+d+1≤F.t)) := by
  intro d a
  let C := F.G.induce K.core
  let O := F.G.induce K.rest
  obtain ⟨pos,account,row,_⟩ := ten_physical_root_deleted_row F paid K
  have bill : matchingEdges C+matchingEdges O<rowCount F.s F.t (F.r+a) := by
    change rowCount F.s F.t (F.r+a)=matchingEdges C+matchingEdges O+d at account
    change 2≤d at pos;omega
  have r := deficient_sum_row_length_dichotomy C O F.n F.m F.pn F.pm row bill
  have b := deficient_sum_row_length_dichotomy C O F.m F.n F.pm F.pn (swap_positive_forcing_row _ _ _ row)
    (by rwa [show rowCount F.t F.s (F.r+a)=rowCount F.s F.t (F.r+a) by simp [rowCount,Nat.add_comm]])
  change F.s≤K.capacity ∨ F.t≤K.outsideRank at r
  change F.t≤K.capacity ∨ F.s≤K.outsideRank at b
  change F.s+F.t-1-(F.r+a)=K.capacity+K.outsideRank+d at account
  change 2≤d at pos
  omega
#print axioms ten_physical_root_deleted_row
#print axioms ten_common_endpoint_guards
#print axioms ten_root_list_length_dichotomy
end JSP452Audit.StarHost
