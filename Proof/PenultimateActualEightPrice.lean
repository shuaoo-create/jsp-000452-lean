import ThreeColumnLossAtDegreeEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem exact_eight_penultimate_price {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (eight:diagonal F.n F.m (F.r+2)-1=8)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8)
    (types:EightSelectionSize (Fintype.card I) (highestWidth F.n F.m F.r))
    (H:EightSevenSixHistory (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ)) :
    let P := ∑i,Nat.card (e i).supp/2
    let k := 2*(F.rank-matchingEdges F.G)
    H.sevenCut.ncard<k ∧ k≤H.sixCut.ncard ∧
      2*P+4*Fintype.card I+1+H.eight.ncard+H.sevenCut.ncard≤
      widthAt F.n F.m F.r 7+widthAt F.n F.m F.r 8+highestWidth F.n F.m F.r := by
  intro P k
  let T := Finset.univ.map e
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  have elements (c) (hc:c∈T) : c∈oddRegularComponents F.G 8 := by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hc;exact actual i
  have card : T.card=Fintype.card I := by simp [T]
  have all := selected_eight_half_orders_fit_six_stage F paid eight T elements (card.symm ▸ types)
  have menu : SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+k) := split_capacities_of_small _ _ (fun i => by
    have room := all (e i) (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    change Nat.card (e i).supp/2≤k at room
    exact room.trans (by omega))
  have miss := admissible_eight_menu_after_high_stages F paid eight e actual types k menu H.eight H.first H.seven H.second
  have short : H.sevenCut.ncard<k := H.counts.1 ▸ miss
  obtain ⟨i,j,_,_,_,_,shape,_,_,_,_⟩ := strict_eight_true_factor_peak F paid eight
  have heads : 0<originalThresholdCount F.n 6 ∨ 0<originalThresholdCount F.m 6 := by
    rcases shape with ⟨_,blue⟩|⟨red,_⟩
    · have := (original_threshold_prefix F.m F.hm 6 j).mp blue.ge;omega
    · have := (original_threshold_prefix F.n F.hn 6 i).mp red.ge;omega
  have cap (x:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤8 := (induced_neighbor_count_le F.G Uᶜ x).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq eight)
  have low := (H.caps cap).2.2
  have fits := (eight_regular_endpoint_sizes F paid eight T elements).2 H.sixCut 6 (by decide)
    (fun v => by have a := low v;change Nat.card ((F.G.induce Uᶜ |>.induce H.sixCutᶜ).neighborSet v)<6;exact Nat.lt_succ_of_le a) heads
  obtain ⟨V,size,price⟩ := H.exact_penultimate_prefix k short fits
  have base := actual_eight_conservative_baseline F paid e actual V (by rw [size];exact menu)
  change rowEnergy F.n F.m (F.r+V.ncard+P)≤(O.induce Vᶜ).edgeSet.ncard ∧
    F.G.edgeSet.ncard=O.edgeSet.ncard+8*P+4*Fintype.card I at base
  change O.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard+6*k+H.eight.ncard+H.sevenCut.ncard at price
  rw [size] at base
  have top : diagonal F.n F.m (F.r+2)=9 := by omega
  have tax := eight_prefix_three_columns F.hs F.ht F.n F.m F.hn F.hm top (k+P)
  rw [←Nat.add_assoc] at tax
  have old := (minimal_rank_exact_source F paid).2.1
  exact ⟨short,fits,by omega⟩

#print axioms exact_eight_penultimate_price
end JSP452Audit.StarHost
