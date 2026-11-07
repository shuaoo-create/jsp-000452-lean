import UnitAxesAccountOnEightExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem actual_eight_selection (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) :
    ∃j:ℕ,0<j ∧ EightSelectionSize j (highestWidth F.n F.m F.r) ∧
      ∃e:Fin j↪F.G.ConnectedComponent,∀i,e i∈oddRegularComponents F.G 8 := by
  classical
  let h := highestWidth F.n F.m F.r
  let Z := oddRegularComponents F.G 8
  have inv := strict_eight_inventory F paid eight
  have reduced := eight_original_interpolated_cases F paid eight
  have pos := strict_eight_has_odd_regular_component F paid eight
  have target : ∃j:ℕ,0<j ∧ EightSelectionSize j h ∧ j≤Z.ncard := by
    have le : h≤minimumExposure F.G 8 := inv.2.1
    have bound := inv.2.2.2.1
    by_cases single:h=1
    · exact ⟨1,by decide,Or.inl ⟨rfl,single⟩,pos⟩
    have hp : 1≤h := inv.1
    have two : 2≤Z.ncard := reduced.2.2.2.2 (by omega)
    by_cases small:h≤4
    · exact ⟨2,by decide,Or.inr (Or.inl ⟨rfl,small⟩),two⟩
    have rho : minimumExposure F.G 8=5 := by omega
    have five : Z.ncard=5 := (reduced.1 rho).1
    exact ⟨3,by decide,Or.inr (Or.inr ⟨rfl,by omega⟩),by omega⟩
  obtain ⟨j,hj,type,room⟩ := target
  let _ := Fintype.ofFinite ↥Z
  have fit : Fintype.card (Fin j)≤Fintype.card ↥Z := by rw [Fintype.card_fin,←Nat.card_eq_fintype_card];exact room
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le fit
  exact ⟨j,hj,type,f.trans (Function.Embedding.subtype _),fun i => (f i).property⟩

theorem strict_eight_no_seven_head (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) : (∀i,F.n i≤6) ∧ (∀j,F.m j≤6) := by
  classical
  have no : ¬(0<originalThresholdCount F.n 7 ∨ 0<originalThresholdCount F.m 7) := by
    intro heads
    obtain ⟨j,positive,types,e,actual⟩ := actual_eight_selection F paid eight
    let _ : Nonempty (Fin j) := ⟨⟨0,positive⟩⟩
    let T := Finset.univ.map e
    let U := componentVertices F.G T
    have elements (c) (hc:c∈T) : c∈oddRegularComponents F.G 8 := by obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hc;exact actual i
    have ft : EightSelectionSize (Fintype.card (Fin j)) (highestWidth F.n F.m F.r) := by rwa [Fintype.card_fin]
    have card : T.card=j := by simp [T]
    have len := (eight_regular_endpoint_sizes F paid eight T elements).1
    have dpos := (minimal_strict_source_deficit F paid).2.2
    have axes (l:ℕ) (lo:1≤l) (hi:l≤7) : ∃x y,WinsHeight F.n F.m F.r l x y ∧ (x=1 ∨ y=1) := by
      have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht lo hi
      change matchingEdges (F.G.induce U)+F.r+2*(F.rank-matchingEdges F.G)≤min F.s F.t at len
      have live : 0<widthAt F.n F.m F.r l := by omega
      obtain ⟨x,y,xp,yp,ht,rr,bb,wide⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm lo live
      have win : WinsHeight F.n F.m F.r l x y := ⟨xp,yp,ht,rr,bb,wide⟩
      refine ⟨x,y,win,?_⟩
      by_contra! neither
      exact eight_high_head_excludes_mixed_winner F paid eight e actual ft heads l x y (by omega) hi (by omega) (by omega) win
    exact eight_all_axes_contradict_selected_stage F paid eight T elements (card.symm ▸ types) axes
  constructor
  · intro i;by_contra! big
    have mem := (original_threshold_prefix F.n F.hn 7 i).mp big
    exact no (Or.inl (by omega))
  · intro j;by_contra! big
    have mem := (original_threshold_prefix F.m F.hm 7 j).mp big
    exact no (Or.inr (by omega))

#print axioms actual_eight_selection
#print axioms strict_eight_no_seven_head
end JSP452Audit.StarHost
