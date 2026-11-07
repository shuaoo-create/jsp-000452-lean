import EveryChosenHalfOrderFitsTwoDeficits
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem admissible_eight_menu_after_high_stages {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (eight:diagonal F.n F.m (F.r+2)-1=8)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8)
    (types:EightSelectionSize (Fintype.card I) (highestWidth F.n F.m F.r))
    (k:ℕ) (menu:SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+k))
    (B:Set ↥((componentVertices F.G (Finset.univ.map e))ᶜ:Set F.X))
    (first:CompleteDegreeStage (F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ) 8 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage ((F.G.induce (componentVertices F.G (Finset.univ.map e))ᶜ).induce Bᶜ) 7 C) :
    B.ncard+C.ncard<k := by
  by_contra! fit
  have price := eight_seven_whole_menu_prices F paid eight e actual k menu B first C second fit
  have elements (c) (hc:c∈Finset.univ.map e) : c∈oddRegularComponents F.G 8 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hc;exact actual i
  have shadow := strict_eight_exterior_stage_bound F paid eight (Finset.univ.map e) elements B first
  rw [Finset.sum_map,Finset.card_map,Finset.card_univ] at shadow
  change widthAt F.n F.m F.r 8+Fintype.card I≤(∑i,Nat.card (e i).supp/2)+B.ncard+(22+2*highestWidth F.n F.m F.r)/5 at shadow
  unfold EightSelectionSize at types
  by_cases high:k≤B.ncard
  · rw [min_eq_left high] at price;rcases types with v|v|v <;> omega
  · rw [min_eq_right (by omega : B.ncard≤k)] at price;rcases types with v|v|v <;> omega

theorem eight_high_head_excludes_mixed_winner {I:Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (eight:diagonal F.n F.m (F.r+2)-1=8)
    (e:I↪F.G.ConnectedComponent) (actual:∀i,e i∈oddRegularComponents F.G 8)
    (types:EightSelectionSize (Fintype.card I) (highestWidth F.n F.m F.r))
    (heads:0<originalThresholdCount F.n 7 ∨ 0<originalThresholdCount F.m 7)
    (j a b:ℕ) (lo:2 ≤ j) (hi:j≤7) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) : False := by
  classical
  let T := Finset.univ.map e
  let U := componentVertices F.G T
  let O := F.G.induce Uᶜ
  have elements (c) (mem:c∈T) : c∈oddRegularComponents F.G 8 := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp mem;exact actual i
  have card : T.card=Fintype.card I := by simp [T]
  obtain ⟨B,first⟩ := complete_degree_stage_exists O 8
  obtain ⟨C,second⟩ := complete_degree_stage_exists (O.induce Bᶜ) 7
  have cap (x:↥(Uᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤8 := (induced_neighbor_count_le F.G Uᶜ x).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq eight)
  have low (x) : Nat.card ((O.induce Bᶜ).neighborSet x)≤7 := by
    have less := complete_stage_lowers_cap O 8 B cap first x;omega
  have last (x) : Nat.card (((O.induce Bᶜ).induce Cᶜ).neighborSet x)≤6 := by
    have less := complete_stage_lowers_cap (O.induce Bᶜ) 7 C low second x;omega
  have physical := nested_deletion_cap O B C 6 last
  have many := (eight_regular_endpoint_sizes F paid eight T elements).2 (nestedRemoved B C) 7 (by decide)
    (fun x => by have := physical x;change Nat.card ((O.induce (nestedRemoved B C)ᶜ).neighborSet x)<7;omega) heads
  rw [nested_removed_card] at many
  have sizes := mixed_eight_winner_caps_every_selected_order F paid eight T elements (card.symm ▸ types) heads j a b lo hi ra bl win
  let k := B.ncard+C.ncard
  have menu : SplitCapacities (fun i => Nat.card (e i).supp/2) (F.r+k) := split_capacities_of_small _ _ (fun i => by
    have bound := sizes (e i) (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    change Nat.card (e i).supp/2≤F.r+(B.ncard+C.ncard)+1;omega)
  have short := admissible_eight_menu_after_high_stages F paid eight e actual types k menu B first C second
  exact (Nat.lt_irrefl k) short

#print axioms admissible_eight_menu_after_high_stages
#print axioms eight_high_head_excludes_mixed_winner
end JSP452Audit.StarHost
