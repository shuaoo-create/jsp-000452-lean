import SixDegreeThreePieceSelection
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_positive_weight_ceiling (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (K:DegreeRegion F.G 6) :
    edgeSurplus (F.G.induce K.positiveCore) 6≤(highestWidth F.n F.m F.r:ℤ)+8 := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  let h := highestWidth F.n F.m F.r
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤6 := (degree v).trans_eq six
  have hpos := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row degree).1
  have hposZ : (1:ℤ)≤h := by exact_mod_cast hpos
  have total := K.piece_weight_sum
  by_contra! missed
  change (h:ℤ)+8<edgeSurplus (F.G.induce K.positiveCore) 6 at missed
  have heavy : 9<∑c:↥K.positive,K.pieceWeight c := by rw [←total];omega
  obtain ⟨T,many,ord,keep,c,member,largest⟩ := omit_three_highest_capacities K.pieceCapacity K.pieceWeight
    (fun i => (K.positive_piece_bounds cap i).2.1) heavy
  let Z := K.pieceCapacity c
  let b := Z-(F.r+1)
  obtain ⟨U,size,indep,full,away⟩ := six_selected_outside K T Z b many
    (fun i hi => ord i hi c member) cap (Nat.sub_le _ _)
  have small (i) (hi:i∈T) : K.pieceCapacity i≤F.r+U.ncard+1 := by
    have ub := largest i hi
    change K.pieceCapacity i≤Z at ub
    rw [size];dsimp [b];omega
  obtain ⟨next,saving⟩ := K.selected_menu_saving T U _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) indep full away small F.row
  have nonzero := (K.positive_piece_bounds cap c).2.2.2
  have some := Finset.single_le_sum (f:=K.pieceCapacity) (fun i _ => Nat.zero_le _) member
  have step : 0<U.ncard+∑i∈T,K.pieceCapacity i := by omega
  have top : diagonal F.n F.m (F.r+2)=7 := by omega
  have price := smaller_source_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G _ F.r _ 6
    F.rank paid F.live le_rfl step top.le (by simpa [Nat.add_assoc] using next) _ saving
  rw [show 6+1=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price
  have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  change (rowEnergy F.n F.m F.r:ℤ)+(∑i∈T,K.pieceWeight i)≤(F.G.edgeSet.ncard:ℤ)+h at price
  rw [←total] at keep
  omega

#print axioms strict_six_positive_weight_ceiling
end JSP452Audit.StarHost
