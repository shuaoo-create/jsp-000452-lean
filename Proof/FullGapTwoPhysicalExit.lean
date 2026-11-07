import FullRetainedCommonRectangles
import Mathlib.Tactic.ClearExcept
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 800000 in
theorem full_gap_two_impossible {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=D-2) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (esc : matchingEdges (G.induce K.core)<s)
    (inner : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+(matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)
      ≤s-matchingEdges (G.induce K.core))
    (width : highestWidth n m r≤minimumExposure G D) (res : minimumExposure G D+1≤d)
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2)
    (kinds : SingleUnpaidKinds G K n m ht r) (witness : LocalPureWitness G K n m ht r) : False := by
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let W := componentBudget H n
  let S := s-μ
  let δ := μ-W.loss
  let A := originalThresholdCount n 2
  let c := originalThresholdCount (W.entries n) 2
  let V := μ+c-A
  let q := μ+1-t
  let f := originalThresholdCount n 3
  let B := originalThresholdCount m 2
  let g := originalThresholdCount m (D-2)
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let L := widthAt n m r
  let Q := jointPhysicalInventory G K
  let U := uniformEnvelope (G.induce K.rest)
  let Z := uniformEnvelope (eraseInternal G K.core)
  change μ<s at esc;change h≤ρ at width;change ρ+1≤d at res
  change t+d+2*(∑j,(m j-1)/2)≤μ+1 at inner
  change a+r+2*(d+∑i,(n i-1)/2)≤t at endpoint
  change a+r+2*(d+∑j,(m j-1)/2)+δ≤S at guard
  have lenS : s=S+μ := by dsimp [S];clear * - esc;omega
  have qeq : q+t=μ+1 := by dsimp [q];clear * - inner;omega
  obtain ⟨j,lo,hi,_,won,_,_,_,_,blueprice⟩ := witness
  have j3 : j=3 := by rw [opp] at hi;clear * - hi lo deg;omega
  rw [j3] at won blueprice
  have price3 := won.2.2.2.2.2
  rw [original_threshold_one m pm] at price3
  change L 3=f+t-1-r at price3
  have pure := blueprice (by clear * - opp deg;omega)
  change s+originalThresholdCount m 3≤f+t at pure
  have p := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have gpos : 0<g := (original_threshold_prefix m hm (D-2) ⟨0,ht⟩).1 opp.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by clear * - opp deg;omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by clear * -;omega) p bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change originalThresholdCount n D+B-1-r≤h at rect
  have budget : (∑i,(n i-1)/2)+B≤t := by clear * - rect width res endpoint p;omega
  obtain ⟨last,bshape⟩ := gap_two_last_columns hs ht n m hn hm pn pm deg live top head opp budget
  have gcap : g≤r := large_opposite_prefix_before_offset hs n m hm head top (by clear * - deg;omega : 3≤D-2)
  have winner := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by clear * - deg;omega))
  obtain ⟨fit,redB,blueB,blueZ,mixB⟩ := high_boundary_retained_rectangles G K n m hn hm pn pm ht esc d data nonunit bpos gpos
  change c+g-1-(r+a)≤U (D-2+1) at mixB
  rw [(gap_two_level_eq D deg).1] at mixB
  change W.loss≤μ at fit
  have len : W.len+μ=s+δ := by dsimp only [RemovalBudget.len,δ];clear * - fit esc;omega
  have fits : t+(∑j,(m j-1)/2)≤μ := by clear * - inner res;omega
  have repair2 := (even_cut_both_envelopes G K n m hn hm pn pm ht row fits 2 (by decide)).2
  have repair3 := even_cut_both_envelopes G K n m hn hm pn pm ht row fits 3 (by decide)
  obtain ⟨floor,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change A≤W.loss+c at floor
  have balance : V+A=μ+c := by dsimp [V];clear * - floor fit;omega
  obtain ⟨l2,l3,lD,lb⟩ := retained_gap_two_layer_prices s t r a μ S A c V q δ W.len B g f (L 2) (L 3) (L (D-1)) (L D)
    (U 2) (Z 2) (U 3) (Z 3) (U (D-1)) (Z (D-1)) (U D) (Z D)
    (by clear * - endpoint res;omega) (by clear * - guard lenS res;omega) qeq balance len lenS gcap winner price3 last bshape redB blueB blueZ repair2 repair3 mixB
  have vol := nonunit_slot_volume G K n hn
  change 3*A≤3*c+2*μ+a+ρ at vol
  have rankV := removal_volume_guard G K n pn
  change μ≤s-A+a+ρ+3*δ at rankV
  have fd := original_threshold_le_length n 2
  change A≤s at fd
  have half := half_extra_pays_large_threshold n (show 3≤3 by decide)
  change f≤∑i,(n i-1)/2 at half
  have pays := gap_two_four_prices μ a r d h ρ t S c V q f δ (L 2) (L 3) (L (D-1)) (L D)
    (Q 2) (Q 3) (Q (D-1)) (Q D) width res qeq (by clear * - inner qeq;omega) (by clear * - endpoint half;omega) (by clear * - guard;omega)
    (by clear * - rankV lenS balance fd;omega) (by clear * - vol balance;omega)
    (by clear * - pure lenS;omega) (by dsimp [δ];clear * - floor balance fit;omega) l2 l3 lD lb
  have rest (j:ℕ) (lo:4≤j) (hi:j≤D-2) : 2*L j≤Q j :=
    (gap_two_middle_basic_paid G K n m hs ht hn hm pn pm deg head opp top d (by change h<d;clear * - width res;omega) (by change t+d≤μ+1;clear * - inner;omega) kinds j lo hi).trans
    (physical_dominates_basic G K n m hn hm pn pm ht esc d data j (lt_of_lt_of_le (by decide : 0<4) lo))
  have full := gap_two_fold_four D h ρ d L Q deg pays rest
  have raw := strict_two_interior_inventories G K n m hs ht hn hm pn pm (by clear * - deg;omega) cap top d rank strict
  have inventory := joint_physical_sum G K
  change (∑z∈Finset.range (D-1),Q (z+2))=_ at inventory
  rw [inventory] at full
  change 2*interiorArea n m r D+2*h+2*d≤(D-1)*(a+2*μ)+interiorInventory (G.induce K.rest) D+
    interiorInventory (eraseInternal G K.core) D+D*ρ at full
  change (D-1)*(a+2*μ)+D*ρ+(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest+
    interiorInventory (G.induce K.rest) D+interiorInventory (eraseInternal G K.core) D<2*interiorArea n m r D+2*h+2*d at raw
  clear * - raw full
  omega

#print axioms full_gap_two_impossible
end JSP452Audit.StarHost