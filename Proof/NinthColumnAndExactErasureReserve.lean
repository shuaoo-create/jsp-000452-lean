import TheNinthColumnOnAdaptedPortEdges
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_general_ninth_column (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (H : ThreeDegreeStages R.erased 7) :
    let L := widthAt F.n F.m F.r 9
    let h := highestWidth F.n F.m F.r
    L≤uniformEnvelope R.erased 9+R.slotDamage 2+(h-1) ∧
      L-H.upper.ncard≤R.slotDamage 2+
        max (h-1) (minimumExposure (R.erased.induce H.upperᶜ) 8) := by
  intro L h
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have rn (i) : F.n i+2≤10 := by have limit := red i;rw [nine] at limit;omega
  have bm (j) : F.m j+2≤10 := by have limit := blue j;rw [nine] at limit;omega
  have restoration := strict_nine_ninth_column_restoration F paid nine R 2 rn bm
  exact ⟨restoration.1,restoration.2 H.upper (H.degree_caps (nine_erased_degree_cap F paid nine R)).1⟩

theorem strict_nine_port_column_account (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (tax : ℕ→ℕ)
    (prices : ∀j,2≤j → j≤9 → widthAt F.n F.m F.r j≤uniformEnvelope R.erased j+tax j) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G
    8*P+9+R.portCount+envelopeReserve R.erased 8≤
      d+highestWidth F.n F.m F.r+(∑i∈Finset.range 8,tax (i+2)) := by
  intro P d
  have cap (x : F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have edge := (R.adapted_edge_account cap).2.2
  change F.G.edgeSet.ncard=R.erased.edgeSet.ncard+9*P+8+R.portCount at edge
  have split := R.exact_port_partition.2.1
  change matchingEdges R.erased+P=matchingEdges F.G at split
  have below := (minimal_rank_exact_source F paid).2.2.1
  have rank : matchingEdges F.G+d=F.rank := by dsimp only [d];omega
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=9) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 9+highestWidth F.n F.m F.r at area
  have reserve := (envelope_reserve_account R.erased 8).1
  change envelopeReserve R.erased 8+(matchingEdges R.erased+interiorInventory R.erased 9)=R.erased.edgeSet.ncard at reserve
  have sum := Finset.sum_le_sum (s:=Finset.range 8) (fun j hj => prices (j+2) (by omega) (by have := Finset.mem_range.mp hj;omega))
  rw [Finset.sum_add_distrib] at sum
  change interiorArea F.n F.m F.r 9 ≤ interiorInventory R.erased 9+(∑i∈Finset.range 8,tax (i+2)) at sum
  have strict := F.strict
  omega

#print axioms strict_nine_general_ninth_column
#print axioms strict_nine_port_column_account
end JSP452Audit.StarHost
