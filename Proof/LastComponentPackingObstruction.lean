import LastSixWinnerTwoFive
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem last_two_five_palette_width {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    (R:SimpleGraph Y) (sub:R≤C) {s t r a L:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (win:L=originalThresholdCount n 2+originalThresholdCount m 5-1-r) (blue:0<originalThresholdCount m 5)
    (bound:originalThresholdCount m 5≤r) (redPrice:UniformPackCap R 2 a) (noBlue:UniformPackCap (C \ R) 5 0)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) : ExactTypedWidth O 2 5 (L-a) := by
  by_cases dead:L≤a
  · exact Or.inl (by omega)
  have live : a<originalThresholdCount n 2 := by omega
  have price := palette_retains_typed_rectangle O C R sub n m hn hm (by decide : 0<2) (by decide : 0<5)
    redPrice noBlue live blue row
  simpa only [←win,Nat.sub_zero] using price

theorem strict_last_component_packing_obstruction (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (mem:c∈oddRegularComponents F.G 6)
    (R:SimpleGraph c.supp) (sub:R≤c.toSimpleGraph) (a:ℕ)
    (red:UniformPackCap R 2 a) (blue:UniformPackCap (c.toSimpleGraph \ R) 5 0) :
    matchingEdges c.toSimpleGraph≤a+1 := by
  let O := F.G.induce c.suppᶜ
  let L := widthAt F.n F.m F.r 6
  obtain ⟨B,out⟩ := complete_degree_stage_exists O 6
  have exactL := single_five_head_shadow_exact F paid six c mem B out
  obtain ⟨_,_,_,_,_,_,exposure⟩ := last_six_residual_certificate F paid six c mem B out
  change minimumExposure (O.induce Bᶜ) 5≤4 at exposure
  have cap (v:↥(c.suppᶜ:Set F.X)) := (induced_neighbor_count_le F.G c.suppᶜ v).trans (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq six)
  have low (v) : Nat.card ((O.induce Bᶜ).neighborSet v)≤5 := by have := complete_stage_lowers_cap O 6 B cap out v;omega
  have closed : ∀x∈c.supp,∀y,F.G.Adj x y → y∈c.supp := fun _ hx _ e => (c.mem_supp_congr_adj e).mp hx
  have row := closed_union_sum_row F.G c.supp closed F.row
  obtain ⟨_,_,n5,m5⟩ := six_degree_head_count_guards F paid six
  have ordinary : ExactTypedWidth O 2 5 (L-a) := by
    rcases last_six_winner_two_five F paid six c mem with best|best
    · exact last_two_five_palette_width O c.toSimpleGraph R sub F.n F.m F.hn F.hm best.2.2.2.2.2
        best.2.2.2.2.1 m5 red blue row
    · have win := best.2.2.2.2.2.trans (by rw [Nat.add_comm (originalThresholdCount F.n 5)])
      exact last_two_five_palette_width O c.toSimpleGraph R sub F.m F.n F.hm F.hn win best.2.2.2.1 n5 red blue
        (swap_positive_forcing_row _ _ _ row)
  have kept := typed_width_after_deletion O B (by decide : 0<2) (by decide : 0<5) ordinary
  have cost := typed_five_exposure_floor (O.induce Bᶜ) low (by decide : 0<2) (by decide : 0<5) rfl kept
  change L-a-B.ncard≤minimumExposure (O.induce Bᶜ) 5 at cost
  change L=matchingEdges c.toSimpleGraph+B.ncard+3 at exactL
  omega

theorem strict_last_component_has_nine_vertices (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (c:F.G.ConnectedComponent) (mem:c∈oddRegularComponents F.G 6) :
    matchingEdges c.toSimpleGraph=4 ∧ Nat.card c.supp=9 ∧ c.toSimpleGraph.edgeSet.ncard=27 := by
  obtain ⟨low,order,_,edges⟩ := strict_six_true_component_capacity F paid six c mem
  have pack := uniform_pack_order_cap c.toSimpleGraph 2 (by decide) Set.univ (fun _ _ _ => Set.mem_univ _)
  rw [Set.ncard_univ] at pack
  have need := strict_last_component_packing_obstruction F paid six c mem c.toSimpleGraph le_rfl _ pack
    (by rw [sdiff_self];exact uniform_pack_bot_cap _ (by decide))
  change matchingEdges c.toSimpleGraph≤Nat.card c.supp/3+1 at need
  exact ⟨by omega,by omega,by omega⟩

#print axioms last_two_five_palette_width
#print axioms strict_last_component_packing_obstruction
#print axioms strict_last_component_has_nine_vertices
end JSP452Audit.StarHost
