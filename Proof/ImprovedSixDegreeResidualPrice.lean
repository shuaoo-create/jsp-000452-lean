import ShortGlobalStageProjectsToEightExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_exposure_three_piece_price {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    {X:Type u} [Finite X] (G:SimpleGraph X) (r N:ℕ)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (live:0<rowCount s t r) (upper:rowCount s t r≤N)
    (paid:AllSmallerPaid.{u} N) (cap:∀x,Nat.card (G.neighborSet x)≤6) (height:diagonal n m (r+2)≤7)
    (exposed:4≤minimumExposure G 6) :
    3*(minimumExposure G 6:ℤ)-(widthAt n m r 7:ℤ)-9≤(G.edgeSet.ncard:ℤ)-(rowEnergy n m r:ℤ) := by
  classical
  obtain ⟨K⟩ := degreeRegion_exists G 6
  let _ := Fintype.ofFinite ↥K.positive
  have total := K.piece_weight_sum
  have weight := K.weight_identity cap
  have dom := positivePieces_dominate G K.barrier K.pieces 6
  change edgeSurplus (G.induce K.core) 6≤edgeSurplus (G.induce K.positiveCore) 6 at dom
  have lower : 3*(minimumExposure G 6:ℤ)≤edgeSurplus (G.induce K.positiveCore) 6 := by omega
  have heavy : 9<∑c:↥K.positive,K.pieceWeight c := by rw [←total];omega
  obtain ⟨T,many,ord,keep,c,member,largest⟩ := omit_three_highest_capacities K.pieceCapacity K.pieceWeight
    (fun i => (K.positive_piece_bounds cap i).2.1) heavy
  let Z := K.pieceCapacity c
  let b := Z-(r+1)
  obtain ⟨U,size,indep,full,away⟩ := six_selected_outside K T Z b many
    (fun i hi => ord i hi c member) cap (Nat.sub_le _ _)
  have small (i) (hi:i∈T) : K.pieceCapacity i≤r+U.ncard+1 := by
    have ub := largest i hi
    change K.pieceCapacity i≤Z at ub
    rw [size];dsimp [b];omega
  obtain ⟨next,saving⟩ := K.selected_menu_saving T U _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) indep full away small row
  have nonzero := (K.positive_piece_bounds cap c).2.2.2
  have some := Finset.single_le_sum (f:=K.pieceCapacity) (fun i _ => Nat.zero_le _) member
  have step : 0<U.ncard+∑i∈T,K.pieceCapacity i := by omega
  have price := smaller_source_price hs ht n m hn hm pn pm G _ r _ 6 N paid live upper step height
    (by simpa [Nat.add_assoc] using next) _ saving
  change (rowEnergy n m r:ℤ)+(∑i∈T,K.pieceWeight i)≤(G.edgeSet.ncard:ℤ)+(widthAt n m r 7:ℤ) at price
  rw [←total] at keep
  omega

theorem exposed_vertex_incidence_bound {X:Type*} [Finite X] (G:SimpleGraph X) (D:ℕ) :
    D*minimumExposure G D≤2*G.edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite X
  obtain ⟨M,_,_,opt⟩ := minimumExposure_attained G D
  let W := exposedFull G M D
  have full := degree_sum_full G W D (fun x hx => hx.2)
  have sum := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun x:X => Nat.card (G.neighborSet x))
    (Finset.subset_univ W.toFinite.toFinset) (fun _ _ _ => Nat.zero_le _)
  have total := G.sum_degrees_eq_twice_card_edges
  have ed : G.edgeFinset.card=G.edgeSet.ncard := by rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card]
  change originalDegreeSum G W≤∑x:X,Nat.card (G.neighborSet x) at sum
  rw [full] at sum
  rw [ed] at total
  have degree (x:X) : Nat.card (G.neighborSet x)=G.degree x := by rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
  simp_rw [degree] at sum
  rw [←opt]
  exact sum.trans_eq total

#print axioms six_exposure_three_piece_price
#print axioms exposed_vertex_incidence_bound
end JSP452Audit.StarHost
