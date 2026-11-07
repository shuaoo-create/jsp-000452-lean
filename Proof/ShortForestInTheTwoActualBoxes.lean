import NineDegreeRootDeletedOriginalRow
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem forest_point_endpoint_on_left {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r:ℕ} (hs:0<s) (legal:r<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    ForestMatchingEndpoint O n (t-r-matchingEdges C) := by
  intro R sub
  have orig := row 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  have bot : (⊥:SimpleGraph Y)≤C := bot_le
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors sub bot
  rcases orig _ both with first|second
  · left
    have eq : (fun i:Fin s => padDemand n (0+i.val))=n := by
      funext i; simp [padDemand,i.isLt]
    change (forest (fun i:Fin s => padDemand n (0+i.val))).IsContained _ at first
    rw [eq] at first
    exact copy_in_left_summand R _ (forest_has_neighbor n pn) first
  · right
    rw [comp,sdiff_bot] at second
    have rank := forest_copy_matching _ (fun j:Fin (t-r) => padDemand m (r+j.val))
      (fun j => pad_positive m pm _ (by have := j.isLt;omega)) second
    rw [Fintype.card_fin,matchingEdges_sumGraph] at rank
    omega

theorem strict_nine_short_box_endpoint (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) (R:NinePortRegion F.G) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    let Q := F.G.induce R.chosen
    let q := P-F.s+d+1
    let k := P-F.t+d+1
    (F.s≤P → ForestMatchingEndpoint Q F.n q ∧ q≤P ∧ F.s+2*(∑i,(F.n i-1)/2)+d≤P+1) ∧
    (F.t≤P → ForestMatchingEndpoint Q F.m k ∧ k≤P ∧ F.t+2*(∑i,(F.m i-1)/2)+d≤P+1) := by
  intro P d Q q k
  let O := F.G.induce R.outside
  let r := F.r+R.roots.ncard
  obtain ⟨positive,balance,row,_⟩ := strict_nine_root_deleted_row F paid nine R
  change 2≤d at positive
  change F.s+F.t-1-r=P+R.outsideRank+d at balance
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have rank := (R.region_rank_edges cap).1
  change matchingEdges Q=P at rank
  constructor
  · intro inside
    have legal : r<F.t := by omega
    have endpt := forest_point_endpoint_on_left Q O F.hs legal F.n F.m F.pn F.pm row
    have eq : F.t-r-matchingEdges O=q := by change F.t-r-R.outsideRank=P-F.s+d+1;omega
    rw [eq] at endpt
    have upper := endpt ⊥ bot_le
    have no : ¬(forest F.n).IsContained (⊥:SimpleGraph ↥R.chosen) := by
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
    have no : ¬(forest F.m).IsContained (⊥:SimpleGraph ↥R.chosen) := by
      rintro ⟨f⟩
      let i : Fin F.t := ⟨0,F.ht⟩
      let j : Fin (F.m i) := ⟨0,F.pm i⟩
      exact f.toHom.map_adj (starEdge F.m ⟨i,j⟩)
    have max := upper.resolve_left no;rw [sdiff_bot,rank] at max
    have account : matchingEdges Q+d+1=F.t+k := by rw [rank];dsimp [k];omega
    have half := endpoint_forest_parity_cost Q F.m F.pm endpt (by omega) (by dsimp [k];omega) (rank.symm ▸ max) account
    dsimp [k] at half
    exact ⟨endpt,max,by omega⟩

#print axioms forest_point_endpoint_on_left
#print axioms strict_nine_short_box_endpoint
end JSP452Audit.StarHost
