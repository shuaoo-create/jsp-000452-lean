import MaxWeightPiecesAreOriginalComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem bounded_subset_piece_sum {I:Type*} [Finite I] (w:I→ℤ) (cap:∀i,w i≤3) (T:Finset I) :
    (∑i∈T,w i)≤2*(T.card:ℤ)+(({i|w i=3}:Set I).ncard:ℤ) := by
  classical
  have per (i:I) : w i≤2+(if w i=3 then (1:ℤ) else 0) := by
    have le := cap i
    split_ifs <;> omega
  have count := Finset.sum_le_sum (s:=T) (fun i _ => per i)
  rw [Finset.sum_add_distrib] at count
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.sum_boole] at count
  have members : (↑(T.filter (fun i => w i=3)):Set I)⊆{i|w i=3} := fun _ mem => (Finset.mem_filter.mp mem).2
  have bound := Set.ncard_le_ncard members
  rw [Set.ncard_coe_finset] at bound
  omega

theorem strict_six_selected_weight_lt {F:StrictFamily.{u}} (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (K:DegreeRegion F.G 6)
    [Fintype ↥K.positive] [DecidableEq ↥K.positive] (T:Finset ↥K.positive)
    (many:Tᶜ.card=3) (ord:∀y∈Tᶜ,∀x∈T,K.pieceCapacity x≤K.pieceCapacity y)
    (c:↥K.positive) (mem:c∈T) (largest:∀i∈T,K.pieceCapacity i≤K.pieceCapacity c) :
    (∑i∈T,K.pieceWeight i)<(highestWidth F.n F.m F.r:ℤ) := by
  have orig := (minimal_rank_exact_source F paid).2.2.2.1
  have cap (v:F.X) := (orig v).trans_eq six
  let Z := K.pieceCapacity c
  let b := Z-(F.r+1)
  obtain ⟨U,size,ind,full,away⟩ := six_selected_outside K T Z b many (fun i hi => ord i hi c mem) cap (Nat.sub_le _ _)
  have small (i) (hi:i∈T) : K.pieceCapacity i≤F.r+U.ncard+1 := by
    have ub := largest i hi
    change K.pieceCapacity i≤Z at ub
    rw [size];dsimp [b];omega
  obtain ⟨next,saving⟩ := K.selected_menu_saving T U _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) ind full away small F.row
  have positive := (K.positive_piece_bounds cap c).2.2.2
  have one := Finset.single_le_sum (f:=K.pieceCapacity) (fun i _ => Nat.zero_le _) mem
  have step : 0<U.ncard+∑i∈T,K.pieceCapacity i := by omega
  have top : diagonal F.n F.m (F.r+2)=7 := by omega
  have price := smaller_source_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G _ F.r _ 6
    F.rank paid F.live le_rfl step top.le (by simpa [Nat.add_assoc] using next) _ saving
  rw [show 6+1=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price
  have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  omega

theorem strict_six_saturated_weight_ceiling (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (K:DegreeRegion F.G 6) :
    edgeSurplus (F.G.induce K.positiveCore) 6+1≤(highestWidth F.n F.m F.r:ℤ)+6+
      ((oddRegularComponents F.G 6).ncard:ℤ) := by
  classical
  let _ := Fintype.ofFinite ↥K.positive
  have orig := (minimal_rank_exact_source F paid).2.2.2.1
  have cap (v:F.X) := (orig v).trans_eq six
  have count := full_weight_piece_count K
  have lim (i:↥K.positive) : K.pieceWeight i≤3 := (K.positive_piece_bounds cap i).2.1
  have lo := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row orig).1
  rw [K.piece_weight_sum]
  by_cases few : Fintype.card ↥K.positive≤3
  · have bound := bounded_subset_piece_sum K.pieceWeight lim Finset.univ
    rw [Finset.card_univ] at bound
    omega
  · have enough : (2:ℤ)*(2+1)<∑_i:↥K.positive,(2:ℤ) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];omega
    obtain ⟨T,_,size,ord,_,c,mem,last⟩ := heavy_piece_selection K.pieceCapacity (fun _ => (2:ℤ)) 2
      (fun _ => by decide) (fun _ => le_rfl) enough
    have kept := strict_six_selected_weight_lt paid six K T size ord c mem last
    have bound := bounded_subset_piece_sum K.pieceWeight lim Tᶜ
    rw [size] at bound
    have total := Finset.sum_add_sum_compl T K.pieceWeight
    omega

#print axioms bounded_subset_piece_sum
#print axioms strict_six_selected_weight_lt
#print axioms strict_six_saturated_weight_ceiling
end JSP452Audit.StarHost
