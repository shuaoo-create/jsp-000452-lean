import ActualFiveHeadAxisFloor
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem mixed_winner_forces_small_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (heads:0<originalThresholdCount F.n 5 ∨ 0<originalThresholdCount F.m 5)
    (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 6) (card:T.card=1)
    (j x y:ℕ) (lo:2≤j) (hi:j≤5) (a:2≤x) (b:2≤y) (win:WinsHeight F.n F.m F.r j x y) :
    matchingEdges (F.G.induce (componentVertices F.G T))≤2*(F.rank-matchingEdges F.G) := by
  let U := componentVertices F.G T
  let P := matchingEdges (F.G.induce U)
  let O := F.G.induce Uᶜ
  let M := chosenSlots F.G T 2
  let N := chosenSlots F.G T 3
  let d := F.rank-matchingEdges F.G
  let tax (i:ℕ) := if i=6 ∨ i=j then M else P
  have h := (strict_six_only_one_original_component F paid six).1
  have enhanced := mixed_low_winner_improves_tax F paid six heads T actual card j x y lo hi a b win
  have sx := (strict_sixth_column_by_slots F paid six T).1
  rw [h] at sx
  have gap := six_slot_saving_per_piece F paid six T actual
  change N+T.card≤M at gap
  change widthAt F.n F.m F.r 6≤uniformEnvelope O 6+max M (N+(1-1)) at sx
  have every := (strict_six_chosen_component_columns F paid six T actual).2.2
  have cuts (i:ℕ) (il:2 ≤ i) (_:i≤6) : widthAt F.n F.m F.r i≤uniformEnvelope O i+tax i := by
    by_cases top:i=6
    · subst i
      rw [show tax 6=M from if_pos (Or.inl rfl)];omega
    by_cases special:i=j
    · subst i
      rw [show tax j=M from if_pos (Or.inr rfl)];exact enhanced
    rw [show tax i=P from if_neg (not_or.mpr ⟨top,special⟩)]
    have pay := every i (by omega)
    rw [card] at pay
    simpa using pay
  have price := six_column_edge_account F paid six T actual tax cuts
  rw [h,card] at price
  have sum : (∑q∈Finset.range 5,tax (q+2))=3*P+2*M := by
    have cases : j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega
    dsimp only [tax]
    rcases cases with eq|eq|eq|eq <;> rw [eq] <;> simp [Finset.sum_range_succ] <;> omega
  rw [sum] at price
  have slots := (strict_chosen_slot_totals F paid six T actual).1
  change 3*M≤2*P+T.card at slots;rw [card] at slots
  change 5*P+3*1+1≤d+1+(3*P+2*M) at price
  change P≤2*d
  omega

theorem short_five_cut_has_only_unit_axes (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (heads:0<originalThresholdCount F.n 5 ∨ 0<originalThresholdCount F.m 5)
    (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 6) (card:T.card=1)
    (H:SixFiveFourHistory (F.G.induce (componentVertices F.G T)ᶜ))
    (short:H.fiveCut.ncard<matchingEdges (F.G.induce (componentVertices F.G T))-(F.r+1)) :
    ∀j,1≤j → j≤5 → ∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1) := by
  let U := componentVertices F.G T
  let P := matchingEdges (F.G.induce U)
  let d := F.rank-matchingEdges F.G
  have need := (strict_exterior_history_cut_bounds F paid six T actual H).2.1 heads
  change 2*d≤H.fiveCut.ncard at need
  change H.fiveCut.ncard<P-(F.r+1) at short
  intro j lo hi
  have floor := lower_axis_at_five_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht lo hi
  have closed := component_vertices_closed F.G T
  have full (v:F.X) (hv:v∈U) : Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1 :=
    ((actual (F.G.connectedComponentMk v) hv).2 v rfl).trans six.symm
  have lens := (strict_closed_union_lengths F paid U closed full).1
  change P+F.r+d+1≤min F.s F.t at lens
  have live : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm lo live
  refine ⟨x,y,win,?_⟩
  by_contra! both
  have detail := win
  obtain ⟨rx,byh,height,_,_,_⟩ := detail
  have bad := mixed_winner_forces_small_component F paid six heads T actual card j x y
    (by omega) hi (by omega) (by omega) win
  change P≤2*d at bad
  omega

#print axioms mixed_winner_forces_small_component
#print axioms short_five_cut_has_only_unit_axes
end JSP452Audit.StarHost
