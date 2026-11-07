import SevenDegreeSignedPeak
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_piece_menu_weight (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (D:ℕ) (top:diagonal F.n F.m (F.r+2)=D+1) (K:DegreeRegion F.G D)
    (T:Finset ↥K.positive) (U:Set F.X) (ind:F.G.IsIndepSet U)
    (full:∀x∈U,Nat.card (F.G.neighborSet x)=D)
    (away:∀c∈T,∀⦃x y:F.X⦄,(wholePiece F.G K.barrier c.val).Adj x y → x∉U)
    (small:∀c∈T,K.pieceCapacity c≤F.r+U.ncard+1)
    (progress:0<U.ncard+∑c∈T,K.pieceCapacity c) :
    (∑c∈T,K.pieceWeight c)<(highestWidth F.n F.m F.r:ℤ) := by
  obtain ⟨row,save⟩ := K.selected_menu_saving T U _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) ind full away small F.row
  have price := smaller_source_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G _ F.r _ D F.rank
    paid F.live le_rfl progress top.le (by simpa [Nat.add_assoc] using row) _ save
  rw [←top,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price
  have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  omega

theorem seven_positive_piece_upper (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) (K:DegreeRegion F.G 7) : K.positive.ncard≤4 := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤7 := (degree v).trans_eq seven
  have h := (strict_seven_original_peak F paid seven).1
  by_contra! tooMany
  have qty : 4<Fintype.card ↥K.positive := by rwa [←Nat.card_eq_fintype_card]
  have heavy : (3:ℤ)*(3+1)<∑_c:↥K.positive,(3:ℤ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];omega
  obtain ⟨T,_,count,ord,_,c,mem,largest⟩ := heavy_piece_selection K.pieceCapacity (fun _ => (3:ℤ)) 3
    (fun _ => by decide) (fun _ => le_rfl) heavy
  let Z := K.pieceCapacity c
  let b := Z-(F.r+1)
  obtain ⟨U,size,ind,full,away⟩ := selected_outside_vertices K T Z b count (fun y hy => ord y hy c mem)
    cap (by dsimp [b];omega)
  have small (y) (hy:y∈T) : K.pieceCapacity y≤F.r+U.ncard+1 := by
    have le := largest y hy
    change K.pieceCapacity y≤Z at le
    rw [size];dsimp [b];omega
  have pos := K.positive_piece_bounds cap c
  have reach := Finset.single_le_sum (f:=K.pieceCapacity) (fun i _ => Nat.zero_le _) mem
  have gain := strict_piece_menu_weight F paid 7 (by omega) K T U ind full away small (by omega)
  rw [h] at gain
  have net := Finset.single_le_sum (f:=K.pieceWeight) (fun i _ => (K.positive_piece_bounds cap i).1.le) mem
  omega

#print axioms strict_piece_menu_weight
#print axioms seven_positive_piece_upper
end JSP452Audit.StarHost
