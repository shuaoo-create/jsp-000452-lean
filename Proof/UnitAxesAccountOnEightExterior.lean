import EightSelectionAgainstTheHighStages
open private JSP452Audit.StarHost.through_degree_split from InteriorHeightArea
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_all_axes_contradict_selected_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (types:EightSelectionSize T.card (highestWidth F.n F.m F.r))
    (axes:∀j,1≤j → j≤7 → ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1)) : False := by
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  let P := ∑c∈T,Nat.card c.supp/2
  let Q := matchingEdges (F.G.induce U)
  let L := widthAt F.n F.m F.r 8
  let h := highestWidth F.n F.m F.r
  have closed := component_vertices_closed F.G T
  have full (x) (hx:x∈U) := ((actual (F.G.connectedComponentMk x) hx).2 x rfl).trans eight.symm
  have cap (v:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet v)≤8 := (induced_neighbor_count_le F.G Uᶜ v).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq eight)
  obtain ⟨B,stage⟩ := complete_degree_stage_exists O 8
  have low := complete_stage_lowers_cap O 8 B cap stage
  obtain ⟨small,hist⟩ := complete_degree_cut_account 7 (O.induce Bᶜ) (fun x => by have := low x;omega)
  obtain ⟨S,last,history⟩ := extend_history_by_first_stage O 7 B stage cap small hist
  have upper := strict_eight_exterior_stage_bound F paid eight T actual B stage
  change L+T.card≤P+B.ncard+(22+2*h)/5 at upper
  have each (i:ℕ) (mem:i∈Finset.range 7) : widthAt F.n F.m F.r (i+1)≤Q+(S (i+1)).ncard :=
    winning_axis_uses_cut_on_exterior F paid closed full (i+1) (by omega) (S (i+1))
      (history.1 _ (by omega) (by have := Finset.mem_range.mp mem;omega)) (axes _ (by omega) (by have := Finset.mem_range.mp mem;omega))
  have costs := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at costs
  have eO := history.2
  rw [Finset.sum_range_succ] at eO
  change O.edgeSet.ncard=(∑i∈Finset.range 7,(S (i+1)).ncard)+(S 8).ncard at eO
  change S 8=B at last
  rw [last] at eO
  have sum := JSP452Audit.StarHost.through_degree_split F.hs F.ht F.n F.m F.pn F.pm F.r 8 (by decide)
  rw [show 8=7+1 by rfl,Finset.sum_range_succ] at sum
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=8) (by omega) (by decide)
  rw [←sum] at area
  change rowEnergy F.n F.m F.r=(∑i∈Finset.range 7,widthAt F.n F.m F.r (i+1))+L+h at area
  have exactPrice := (minimal_rank_exact_source F paid).2.1
  obtain ⟨_,edgeC,rank,_⟩ := regular_union_at_even_degree F.G 4 T actual
  change (F.G.induce U).edgeSet.ncard=8*P+4*T.card at edgeC
  change Q≤P at rank
  have sep := intact_components_plus_exterior F.G U closed
  change F.G.edgeSet.ncard=(F.G.induce U).edgeSet.ncard+O.edgeSet.ncard at sep
  change EightSelectionSize T.card h at types
  clear * - upper costs eO area exactPrice edgeC rank sep types
  unfold EightSelectionSize at types;rcases types with m|m|m <;> omega

#print axioms eight_all_axes_contradict_selected_stage
end JSP452Audit.StarHost
