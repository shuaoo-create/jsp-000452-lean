import AbsentMixedWinnerBelowShortFiveCut
open private JSP452Audit.StarHost.through_degree_split from InteriorHeightArea
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem winning_axis_uses_cut_on_exterior (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {U:Set F.X} (closed:∀v∈U,∀w,F.G.Adj v w → w∈U)
    (full:∀v∈U,Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1)
    (j:ℕ) (positive:0<j) (C:Set ↥(Uᶜ:Set F.X))
    (cut:∀v,Nat.card (((F.G.induce Uᶜ).induce Cᶜ).neighborSet v)<j)
    (axis:∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1)) :
    widthAt F.n F.m F.r j≤matchingEdges (F.G.induce U)+C.ncard := by
  let P := matchingEdges (F.G.induce U)
  let L := widthAt F.n F.m F.r j
  have all := (strict_exterior_parity_and_stages F paid U closed full).2.2
  have limits := all C (j-1) (fun v => by have := cut v;omega)
  have id : j-1+1=j := by omega
  rw [id] at limits
  have lens := (strict_closed_union_lengths F paid U closed full).1
  change P+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t at lens
  have sr := lens.trans (Nat.min_le_left _ _)
  have tr := lens.trans (Nat.min_le_right _ _)
  obtain ⟨x,y,⟨_,_,ht,rx,byh,win⟩,unit⟩ := axis
  change L≤P+C.ncard
  rcases unit with rfl|rfl
  · have same : y=j := by omega
    subst y
    rw [original_threshold_one F.n F.pn] at win
    change L=F.s+originalThresholdCount F.m j-1-F.r at win
    have price := limits.2 byh
    change F.s-F.r-P-1+originalThresholdCount F.m j≤C.ncard at price
    omega
  · have same : x=j := by omega
    subst x
    rw [original_threshold_one F.m F.pm] at win
    change L=originalThresholdCount F.n j+F.t-1-F.r at win
    have price := limits.1 rx
    change F.t-F.r-P-1+originalThresholdCount F.n j≤C.ncard at price
    omega

theorem pure_axes_pay_last_sixth_width (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) (one:T.card=1)
    (B:Set ↥((componentVertices F.G T)ᶜ:Set F.X)) (stage:CompleteDegreeStage (F.G.induce (componentVertices F.G T)ᶜ) 6 B)
    (axes:∀j,1≤j → j≤5 → ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1)) :
    matchingEdges (F.G.induce (componentVertices F.G T))+B.ncard+3≤widthAt F.n F.m F.r 6 := by
  let U := componentVertices F.G T
  let P := matchingEdges (F.G.induce U)
  let O := F.G.induce Uᶜ
  let L := widthAt F.n F.m F.r 6
  have closed := component_vertices_closed F.G T
  have full (v:F.X) (hv:v∈U) : Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1 :=
    ((actual (F.G.connectedComponentMk v) hv).2 v rfl).trans six.symm
  have cap (v:↥(Uᶜ:Set F.X)) := (induced_neighbor_count_le F.G Uᶜ v).trans (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq six)
  obtain ⟨S,final,hist⟩ := six_column_history_starting_at O cap B stage
  have each (i:ℕ) (mem:i∈Finset.range 5) : widthAt F.n F.m F.r (i+1)≤P+(S (i+1)).ncard :=
    winning_axis_uses_cut_on_exterior F paid closed full (i+1) (by omega) (S (i+1))
      (hist.1 _ (by omega) (by have := Finset.mem_range.mp mem;omega)) (axes _ (by omega) (by have := Finset.mem_range.mp mem;omega))
  have cuts := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range] at cuts
  simp only [nsmul_eq_mul,Nat.cast_id] at cuts
  have eO := hist.2
  rw [show 6=5+1 by rfl,Finset.sum_range_succ] at eO
  change O.edgeSet.ncard=(∑i∈Finset.range 5,(S (i+1)).ncard)+(S 6).ncard at eO
  rw [final] at eO
  have sum := JSP452Audit.StarHost.through_degree_split F.hs F.ht F.n F.m F.pn F.pm F.r 6 (by decide)
  rw [show 6=5+1 by rfl,Finset.sum_range_succ] at sum
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=6) (by omega) (by decide)
  have width := (strict_six_only_one_original_component F paid six).1
  rw [width,←sum] at area
  change rowEnergy F.n F.m F.r=(∑i∈Finset.range 5,widthAt F.n F.m F.r (i+1))+L+1 at area
  have original := (minimal_rank_exact_source F paid).2.1
  have cost := (strict_six_chosen_component_columns F paid six T actual).2.1
  rw [one] at cost
  change (F.G.induce U).edgeSet.ncard=6*P+3 at cost
  have edges := intact_components_plus_exterior F.G U closed
  change F.G.edgeSet.ncard=(F.G.induce U).edgeSet.ncard+O.edgeSet.ncard at edges
  change P+B.ncard+3≤L
  clear * - area original eO cuts cost edges
  omega

#print axioms winning_axis_uses_cut_on_exterior
#print axioms pure_axes_pay_last_sixth_width
end JSP452Audit.StarHost
