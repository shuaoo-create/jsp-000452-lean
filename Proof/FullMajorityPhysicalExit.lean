import MajorityRealLowerCharges
import Mathlib.Tactic.ClearExcept
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 800000 in
theorem full_majority_opposite_impossible {s t r D b : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=b) (large : 3≤b) (major : D+1≤2*b) (gap : b+3≤D) (top : diagonal n m (r+2)=D+1)
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
  let B := originalThresholdCount m 2
  let g := originalThresholdCount m b
  let k := D-b
  have tot : b+k=D := by dsimp [k];omega
  have mid : k+1≤b := by clear * - tot major;omega
  have klo : 2≤k := by clear * - tot gap;omega
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
  rw [opp] at hi
  let p₀ := j-3
  let f := originalThresholdCount n j
  have jp : p₀+3=j := by dsimp [p₀];clear * - lo;omega
  have pRange : p₀<k-1 := by clear * - tot hi jp lo;omega
  have price3 := won.2.2.2.2.2
  rw [original_threshold_one m pm] at price3
  change L j=f+t-1-r at price3
  have pure := blueprice (by rw [opp];clear * - mid hi tot;omega)
  change s+originalThresholdCount m j≤f+t at pure
  have p := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have gpos : 0<g := (original_threshold_prefix m hm b ⟨0,ht⟩).1 opp.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by clear * - opp large;omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by clear * -;omega) p bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change originalThresholdCount n D+B-1-r≤h at rect
  have budget : (∑i,(n i-1)/2)+B≤t := by clear * - rect width res endpoint p;omega
  obtain ⟨high,bshape⟩ := full_high_and_boundary_columns hs ht n m hn hm pn pm live top head opp large (by omega) major budget
  let z := b+2+p₀
  have zz : b+2≤z := by dsimp [z];omega
  have ze : z≤D := by dsimp [z];clear * - tot pRange;omega
  have last := high z zz ze
  have gcap : g≤r := large_opposite_prefix_before_offset hs n m hm head top large
  have winner := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by clear * - deg;omega))
  obtain ⟨fit,redB,blueB,blueZ,mixB⟩ := high_boundary_retained_rectangles G K n m hn hm pn pm ht esc d data nonunit bpos gpos
  change c+g-1-(r+a)≤U (b+1) at mixB
  change W.loss≤μ at fit
  have len : W.len+μ=s+δ := by dsimp only [RemovalBudget.len,δ];clear * - fit esc;omega
  have fits : t+(∑j,(m j-1)/2)≤μ := by clear * - inner res;omega
  have repair2 := (even_cut_both_envelopes G K n m hn hm pn pm ht row fits 2 (by decide)).2
  have repair3 := even_cut_both_envelopes G K n m hn hm pn pm ht row fits j (by clear * - lo;omega)
  obtain ⟨floor,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change A≤W.loss+c at floor
  have balance : V+A=μ+c := by dsimp [V];clear * - floor fit;omega
  obtain ⟨l2,l3,lD,lb⟩ := majority_genuine_layer_prices s t r a μ S A c V q δ W.len B g f (L 2) (L j) (L (b+1)) (L z) h
    (U 2) (Z 2) (U j) (Z j) (U (b+1)) (Z (b+1)) (U z) (Z z)
    (by clear * - endpoint res;omega) (by clear * - guard lenS res;omega) qeq balance len lenS gcap winner price3 last bshape redB blueB blueZ repair2 repair3 mixB
  have vol := nonunit_slot_volume G K n hn
  change 3*A≤3*c+2*μ+a+ρ at vol
  have rankV := removal_volume_guard G K n pn
  change μ≤s-A+a+ρ+3*δ at rankV
  have fd := original_threshold_le_length n 2
  change A≤s at fd
  have half := half_extra_pays_large_threshold n lo
  change f≤∑i,(n i-1)/2 at half
  have pays := majority_four_prices μ a r d h ρ t S c V q f δ (L 2) (L j) (L (b+1)) (L z)
    (Q 2) (Q j) (Q (b+1)) (Q z) width res qeq (by clear * - inner qeq;omega) (by clear * - endpoint half;omega) (by clear * - guard;omega)
    (by clear * - rankV lenS balance fd;omega) (by clear * - vol balance;omega)
    (by clear * - pure lenS;omega) (by dsimp [δ];clear * - floor balance fit;omega) l2 l3 lD lb
  have extra := Nat.mul_le_mul_right ρ (show 4≤D by omega)
  have key : 2*L 2+2*L (p₀+3)+2*L (b+1)+2*L (b+2+p₀)+2*h+2*d≤
      Q 2+Q (p₀+3)+Q (b+1)+Q (b+2+p₀)+D*ρ := by
    rw [jp];change 2*L 2+2*L j+2*L (b+1)+2*L z+2*h+2*d≤Q 2+Q j+Q (b+1)+Q z+D*ρ;clear * - pays extra;omega
  have g2 : B≤r+ρ := by clear * - rect width p;omega
  have space : μ+B≤s := by clear * - guard lenS res g2;omega
  have low (v:ℕ) (loV:3≤v) (hiV:v≤b) := majority_real_low_caps G K n m hs ht hn hm pn pm head opp large
    (by omega) top live row esc d data budget space inner (by change h<d;clear * - width res;omega) v loV hiV
  have rest (v:ℕ) (vr:v<b-k-1) : 2*L (k+2+v)≤Q (k+2+v) := by
    have priced := low (k+2+v) (by clear * - klo;omega) (by clear * - mid vr;omega)
    exact priced.2 (by dsimp [k];omega)
  have pair (v:ℕ) (vr:v<k-1) (_ne:v≠p₀) :
      2*L (v+3)+2*L (b+2+v)≤Q (v+3)+Q (b+2+v) := by
    have l := (low (v+3) (by omega) (by clear * - mid vr;omega)).1
    change 2*L (v+3)≤Q (v+3)+2*q at l
    have e := high (b+2+v) (by omega) (by clear * - tot vr;omega)
    change L (b+2+v)≤t-1 at e
    have mass : a+2*μ≤Q (b+2+v) := by
      change a+2*μ≤a+2*μ+U (b+2+v)+Z (b+2+v);omega
    clear * - l e mass qeq ht;omega
  have full := majority_pair_fold D b k p₀ h ρ d L Q tot klo mid pRange key pair rest
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

#print axioms full_majority_opposite_impossible
end JSP452Audit.StarHost