import ActualRowsAndEndpointLengthsAfterDeletingTheTenDegreeRoots
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_short_core_endpoint (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (R:TenBlockPartition F.G) :
    let P := R.capacity
    let d := F.rank-matchingEdges F.G
    let Q := F.G.induce R.core
    let q := P-F.s+d+1
    let k := P-F.t+d+1
    (F.s≤P → ForestMatchingEndpoint Q F.n q ∧ q≤P ∧ F.s+2*(∑i,(F.n i-1)/2)+d≤P+1) ∧
    (F.t≤P → ForestMatchingEndpoint Q F.m k ∧ k≤P ∧ F.t+2*(∑i,(F.m i-1)/2)+d≤P+1) := by
  intro P d Q q k
  let O := F.G.induce R.rest
  let r := F.r+R.roots.ncard
  obtain ⟨positive,balance,row,_⟩ := ten_physical_root_deleted_row F paid R
  change 2≤d at positive
  change F.s+F.t-1-r=P+R.outsideRank+d at balance
  have rank : matchingEdges Q=P := rfl
  constructor
  · intro inside
    have legal : r<F.t := by omega
    have endpt := forest_point_endpoint_on_left Q O F.hs legal F.n F.m F.pn F.pm row
    have eq : F.t-r-matchingEdges O=q := by change F.t-r-R.outsideRank=P-F.s+d+1;omega
    rw [eq] at endpt
    have upper := endpt ⊥ bot_le
    have no : ¬(forest F.n).IsContained (⊥:SimpleGraph ↥R.core) := by
      rintro ⟨f⟩
      let i : Fin F.s := ⟨0,F.hs⟩
      let j : Fin (F.n i) := ⟨0,F.pn i⟩
      exact f.toHom.map_adj (starEdge F.n ⟨i,j⟩)
    have max := upper.resolve_left no;rw [sdiff_bot,rank] at max
    have account : matchingEdges Q+d+1=F.s+q := by rw [rank];dsimp [q];omega
    have half := endpoint_forest_parity_cost Q F.n F.pn endpt (by omega) (by dsimp [q];omega) (rank.symm ▸ max) account
    dsimp [q] at half
    exact ⟨endpt,max,by omega⟩
  · intro inside
    have legal : r<F.s := by omega
    have endpt := forest_point_endpoint_on_left Q O F.ht legal F.m F.n F.pm F.pn (swap_positive_forcing_row _ _ _ row)
    have eq : F.s-r-matchingEdges O=k := by change F.s-r-R.outsideRank=P-F.t+d+1;omega
    rw [eq] at endpt
    have upper := endpt ⊥ bot_le
    have no : ¬(forest F.m).IsContained (⊥:SimpleGraph ↥R.core) := by
      rintro ⟨f⟩
      let i : Fin F.t := ⟨0,F.ht⟩
      let j : Fin (F.m i) := ⟨0,F.pm i⟩
      exact f.toHom.map_adj (starEdge F.m ⟨i,j⟩)
    have max := upper.resolve_left no;rw [sdiff_bot,rank] at max
    have account : matchingEdges Q+d+1=F.t+k := by rw [rank];dsimp [k];omega
    have half := endpoint_forest_parity_cost Q F.m F.pm endpt (by omega) (by dsimp [k];omega) (rank.symm ▸ max) account
    dsimp [k] at half
    exact ⟨endpt,max,by omega⟩


theorem ten_short_core_mass (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (R:TenBlockPartition F.G) :
    let P := R.capacity
    let d := F.rank-matchingEdges F.G
    (F.s≤P → (∑i,F.n i)+d≤P+R.roots.ncard+R.eta) ∧ (F.t≤P → (∑j,F.m j)+d≤P+R.roots.ncard+R.eta) := by
  intro P d
  let C := F.G.induce R.core
  have rank : matchingEdges C=P := rfl
  obtain ⟨red,blue⟩ := ten_short_core_endpoint F paid R
  have size := R.order
  change R.core.ncard=2*P+R.roots.ncard+R.eta at size
  constructor
  · intro le
    obtain ⟨ep,fit,_⟩ := red le
    have spend := endpoint_forest_vertex_budget C F.n F.pn ep (by omega) (rank.symm ▸ fit)
    change F.s+(∑i,F.n i)+(P-F.s+d+1-1)≤R.core.ncard at spend;omega
  · intro le
    obtain ⟨ep,fit,_⟩ := blue le
    have spend := endpoint_forest_vertex_budget C F.m F.pm ep (by omega) (rank.symm ▸ fit)
    change F.t+(∑i,F.m i)+(P-F.t+d+1-1)≤R.core.ncard at spend;omega


#print axioms ten_short_core_endpoint
#print axioms ten_short_core_mass
end JSP452Audit.StarHost
