import SevenPieceWidthArithmetic
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem typed_width_exposure_at_cap {X:Type*} [Finite X] (G:SimpleGraph X) (D a b l:ℕ)
    (pos:0<D) (cap:∀x,Nat.card (G.neighborSet x)≤D)
    (ha:0<a) (hb:0<b) (sum:a+b-1=D+1) (typed:ExactTypedWidth G a b l) :
    l≤minimumExposure G D := by
  rcases typed with zero|⟨u,v,hu,hv,eq,force⟩
  · omega
  · have width := uniform_pair_le_envelope G a b u v (D+1) ha hb hu hv sum force
    rw [eq] at width
    exact width.trans ((uniformEnvelope_le_deletion G D pos).trans (deletionBudget_le_minimumExposure G D pos cap))

namespace SevenPiece
variable (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) (seven:diagonal F.n F.m (F.r+2)-1=7)
    (K:DegreeRegion F.G 7) (p:↥K.positive) (minimum:∀q:↥K.positive,K.pieceCapacity p≤K.pieceCapacity q)
    (S:Descent F K p)

include paid seven minimum in
theorem restored_successor_exposure :
    let Y := (erased F K p).induce S.removedᶜ
    let L := widthAt F.n F.m F.r 7
    let z := K.pieceCapacity p
    let l := L-(2*z+4)/3-cost F K p
    5≤l ∧ l≤minimumExposure Y 6 ∧
      ((Y.edgeSet.ncard:ℤ)-(rowEnergy F.n F.m (nextRow F K p):ℤ))<
        2*(minimumExposure Y 6:ℤ)-(widthAt F.n F.m (nextRow F K p) 7:ℤ)-4 := by
  intro Y L z l
  let t := cost F K p
  let M := (2*z+4)/3
  let w := (K.pieceWeight p).toNat
  have base := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y _ S.row S.smaller
  have up := S.upper
  change (Y.edgeSet.ncard:ℤ)-(rowEnergy F.n F.m (nextRow F K p):ℤ)≤(L:ℤ)-(z:ℤ)-(S.stage.ncard:ℤ)-K.pieceWeight p at up
  have wt := (strict_seven_four_positive_pieces F paid seven K).2.2.2 p
  have cast : (w:ℤ)=K.pieceWeight p := Int.toNat_of_nonneg (by omega)
  have enough : z+S.stage.ncard+w≤L := by omega
  have arithmetic := seven_descent_arithmetic z S.stage.ncard w F.r L
    (seven_minimum_capacity_at_least_seventeen F paid seven K p minimum) S.room S.short (by omega) enough
  change 2*M<L ∧ 5≤l ∧ L-z-t=l-(z-M) ∧
    (L:ℤ)-(z:ℤ)-(S.stage.ncard:ℤ)-(w:ℤ)<2*(l:ℤ)-((L-z-t:ℕ):ℤ)-4 at arithmetic
  obtain ⟨a,b,ha,hb,height,first,second,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by decide : 0<7) (show 0<L by omega)
  have na := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 first
  have mb := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 second
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have nh := red ⟨0,F.hs⟩
  have mh := blue ⟨0,F.ht⟩
  rw [seven] at nh mh
  have typed := typed_width_of_original_rectangle F.G F.n F.m F.hn F.hm first second F.row
  rw [←win] at typed
  have restored := seven_block_restored_typed_width F paid seven K p a b L (by omega) (by omega) typed arithmetic.1
  have actual := typed_width_after_deletion (erased F K p) S.removed ha hb restored
  rw [S.count] at actual
  have exposure := typed_width_exposure_at_cap Y 6 a b l (by decide) S.cap ha hb height actual
  have column := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r (z+t) 7
  change widthAt F.n F.m (nextRow F K p) 7=L-(z+t) at column
  have tax : widthAt F.n F.m (nextRow F K p) 7=L-z-t := by omega
  rw [tax];exact ⟨arithmetic.2.1,exposure,by omega⟩

#print axioms restored_successor_exposure
end SevenPiece
#print axioms typed_width_exposure_at_cap
end JSP452Audit.StarHost
