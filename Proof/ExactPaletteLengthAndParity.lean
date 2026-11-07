import CompleteEndpointOnAnEdgePartition
open private JSP452Audit.StarHost.fd_length_from_choices JSP452Audit.StarHost.fd_rank_choices from FinalDescentLengths
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Any genuine edge partition with additive matching rank yields the complete
forest endpoint on the opposite palette as soon as the other list is longer
than the discarded palette rank. -/
theorem long_list_exact_palette_endpoint {X : Type*} [Finite X] (G J : SimpleGraph X)
    (sub : J≤G) {s t r d : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (pos : 0<d)
    (balance : matchingEdges J+matchingEdges (G \ J)+d=rowCount s t r)
    (long : matchingEdges J<t) :
    let Y := G \ J
    let q := t-r-matchingEdges J
    d+1≤q ∧ s≤matchingEdges Y ∧ matchingEdges Y+d+1=s+q ∧
      ForestMatchingEndpoint Y n q ∧ 2*(d+∑i,(n i-1)/2)≤q := by
  intro Y q
  have row' := swap_positive_forcing_row G _ _ row
  have balance' : matchingEdges J+matchingEdges Y+d=rowCount t s r := by
    simpa only [rowCount,Nat.add_comm t s] using balance
  have length := JSP452Audit.StarHost.fd_length_from_choices hs long pos balance'
    (JSP452Audit.StarHost.fd_rank_choices G _ _ (pad_positive m pm) (pad_positive n pn) row' J sub)
  have live : r<t := by omega
  have hq : d+1≤q := by dsimp only [q];omega
  have account : matchingEdges Y+d+1=s+q := by
    change matchingEdges J+matchingEdges Y+d=s+t-1-r at balance
    dsimp only [q];omega
  have test := edge_palette_forest_endpoint G Y J sdiff_le (by
    intro x y e
    by_cases z : J.Adj x y
    · exact Or.inr z
    · exact Or.inl ⟨e,z⟩) hs live n m pm row
  have fe : ForestMatchingEndpoint Y n q := test
  have parity := endpoint_forest_parity_cost Y n pn fe pos (by omega) (positive_endpoint_rank Y hs n pn fe) account
  exact ⟨hq,length.2,account,fe,parity⟩

theorem strict_nine_actual_erased_endpoints (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (R : NinePortRegion F.G) :
    let P := R.totalCapacity
    let Y := R.erased
    let d := F.rank-matchingEdges F.G
    (P<F.t → let q := F.t-F.r-P
      d+1≤q ∧ F.s≤matchingEdges Y ∧ matchingEdges Y+d+1=F.s+q ∧
      ForestMatchingEndpoint Y F.n q ∧ 2*(d+∑i,(F.n i-1)/2)≤q) ∧
    (P<F.s → let q := F.s-F.r-P
      d+1≤q ∧ F.t≤matchingEdges Y ∧ matchingEdges Y+d+1=F.t+q ∧
      ForestMatchingEndpoint Y F.m q ∧ 2*(d+∑j,(F.m j-1)/2)≤q) := by
  intro P Y d
  have below := (minimal_rank_exact_source F paid).2.2.1
  have pos : 0<d := by dsimp only [d];omega
  obtain ⟨inside,ext,_⟩ := R.exact_port_partition
  have full : matchingEdges R.adapted+matchingEdges Y+d=rowCount F.s F.t F.r := by
    change matchingEdges R.adapted+matchingEdges R.erased+d=F.rank
    dsimp only [d];omega
  constructor
  · intro size
    have q := long_list_exact_palette_endpoint F.G R.adapted R.adapted_le F.hs F.ht F.n F.m
      F.pn F.pm F.row pos full (inside.symm ▸ size)
    simpa only [inside] using q
  · intro size
    have full' : matchingEdges R.adapted+matchingEdges Y+d=rowCount F.t F.s F.r := by
      simpa only [rowCount,Nat.add_comm F.t F.s] using full
    have q := long_list_exact_palette_endpoint F.G R.adapted R.adapted_le F.ht F.hs F.m F.n
      F.pm F.pn (swap_positive_forcing_row _ _ _ F.row) pos full' (inside.symm ▸ size)
    simpa only [inside] using q

#print axioms long_list_exact_palette_endpoint
#print axioms strict_nine_actual_erased_endpoints
end JSP452Audit.StarHost
