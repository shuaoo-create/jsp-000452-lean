import FixOnePositiveSmallerTenDegreeSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem eight_exposure_four_piece_price {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    {X:Type u} [Finite X] (G:SimpleGraph X) (r N:ℕ)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (live:0<rowCount s t r) (upper:rowCount s t r≤N)
    (paid:AllSmallerPaid.{u} N) (cap:∀x,Nat.card (G.neighborSet x)≤8) (height:diagonal n m (r+2)≤9)
    (exposed:5≤minimumExposure G 8) :
    4*(minimumExposure G 8:ℤ)-(widthAt n m r 9:ℤ)-16≤(G.edgeSet.ncard:ℤ)-(rowEnergy n m r:ℤ) := by
  classical
  obtain ⟨K⟩ := degreeRegion_exists G 8
  let _ := Fintype.ofFinite ↥K.positive
  have total := K.piece_weight_sum
  have weight := K.weight_identity cap
  have dom := positivePieces_dominate G K.barrier K.pieces 8
  change edgeSurplus (G.induce K.core) 8≤edgeSurplus (G.induce K.positiveCore) 8 at dom
  have lower : 4*(minimumExposure G 8:ℤ)≤edgeSurplus (G.induce K.positiveCore) 8 := by omega
  have heavy : 16<∑c:↥K.positive,K.pieceWeight c := by rw [←total];omega
  have point (i:↥K.positive) : K.pieceWeight i≤(4:ℤ) := (K.positive_piece_bounds cap i).2.1
  have counted := Finset.sum_le_sum (s:=(Finset.univ:Finset ↥K.positive)) (fun i _ => point i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at counted
  have manyLabels : 4<Fintype.card ↥K.positive := by omega
  obtain ⟨T,many,ord,c,member,largest⟩ := omit_half_cap_largest K.pieceCapacity 4 (by decide) manyLabels
  have omitted := Finset.sum_le_sum (s:=Tᶜ) (fun i _ => point i)
  rw [Finset.sum_const,many] at omitted
  have keep := Finset.sum_add_sum_compl T K.pieceWeight
  norm_num at omitted
  let Z := K.pieceCapacity c
  let b := Z-(r+1)
  obtain ⟨U,size,indep,full,away⟩ := half_cap_spare_vertices 4 (by decide) K T Z b many
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
  have price := smaller_source_price hs ht n m hn hm pn pm G _ r _ 8 N paid live upper step height
    (by simpa [Nat.add_assoc] using next) _ saving
  change (rowEnergy n m r:ℤ)+(∑i∈T,K.pieceWeight i)≤(G.edgeSet.ncard:ℤ)+(widthAt n m r 9:ℤ) at price
  rw [←total] at keep
  omega


#print axioms eight_exposure_four_piece_price
end JSP452Audit.StarHost
