import SameSevenSuccessorExposure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_exposure_price_on_actual_row {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    {X:Type u} [Finite X] (G:SimpleGraph X) (r N:ℕ)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (live:0<rowCount s t r) (upper:rowCount s t r≤N)
    (paid:AllSmallerPaid.{u} N) (cap:∀x,Nat.card (G.neighborSet x)≤6) (height:diagonal n m (r+2)≤7)
    (exposed:5≤minimumExposure G 6) :
    2*(minimumExposure G 6:ℤ)-(widthAt n m r 7:ℤ)-4≤(G.edgeSet.ncard:ℤ)-(rowEnergy n m r:ℤ) := by
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

#print axioms six_exposure_price_on_actual_row
end JSP452Audit.StarHost
