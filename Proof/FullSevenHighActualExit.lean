import FullLowRealSuppressionPrice
import Mathlib.Tactic.ClearExcept
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem seven_high_full_impossible {s t r D b : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 9≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (opp : m ⟨0,ht⟩=b) (large : 2≤b) (gap : 7≤D-b-1) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t) (outside : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : highestWidth n m r≤minimumExposure G D) (res : minimumExposure G D+1≤d)
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2) : False := by
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let C := widthAt n m r
  let Q := jointPhysicalInventory G K
  let f := originalThresholdCount n
  let B := originalThresholdCount m 2
  let q := μ+1-t
  let X₀ := ∑i,(n i-1)/2
  change μ<s at esc
  change t+d+2*(∑j,(m j-1)/2)≤μ+1 at inner
  change a+r+2*(d+X₀)≤t at endpoint;change a+r+2*d≤s-μ at outside
  change h≤ρ at width;change ρ+1≤d at res
  have sub : b<D := by clear * - gap;omega
  have full : 0<f D := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have px : 0<f 2 := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (by clear * - deg head;omega)
  have blue : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by clear * - large opp;omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by omega) full blue
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change f D+B-1-r≤h at rect
  have limit : B≤r+ρ := by clear * - rect width full;omega
  have budget : X₀+B≤t := by clear * - limit res endpoint;omega
  have space : μ+B≤s := by clear * - limit outside res esc;omega
  have before : r<t := by clear * - endpoint res;omega
  have fits : t+∑j,(m j-1)/2≤μ := by clear * - inner res;omega
  have qeq : q+t=μ+1 := by dsimp [q];clear * - fits;omega
  obtain ⟨T,size,_,supp⟩ := actual_full_suppression_floor G K n m hs hn hm pm deg cap head row
  change 13*T.ncard≤4*(2*μ+a+ρ) at size
  let P := max a (2*μ-(a+2*T.ncard))
  have seven : 2*μ≤7*P+2*ρ := (suppression_base_arithmetic μ a ρ T.ncard size).2
  have axis (j:ℕ) (jp:0<j) (jc:j≤D) (w:C j≤f j+t-1-r) : 2*C j+P≤Q j+2*f j := by
    obtain ⟨left,right⟩ := supp j jp jc
    exact suppression_pure_axis_price μ a t r T.ncard (f j) (C j) _ _ (by clear * - fits;omega) w left right
  have low : 2*C 2≤Q 2+q := full_low_physical_price G K n m hs ht hn hm pn pm live row esc d data
    (by clear * - deg;omega) top before fits nonunit blue
  have axes (j:ℕ) (lo:3≤j) (hi:j≤b) : 2*C j≤Q j+2*f j := by
    have leD : j≤D := hi.trans sub.le
    have opts := active_opposite_pure_or_paid G K n m hs ht hn hm pn pm budget space esc j lo (hi.trans_eq opp.symm)
      (actual_height_positive n m live top j (by omega))
    rcases opts with red|paid
    · have price := axis j (by omega) leD red;omega
    · have pay := paid.trans (physical_dominates_basic G K n m hn hm pn pm ht esc d data j (by omega))
      change 2*C j≤Q j at pay;omega
  have border : 2*C (b+1)≤Q (b+1)+2*f (b+1)+2*ρ := by
    rcases full_boundary_pure_or_reserve G K n m hs ht hn hm pn pm opp top live large sub budget esc ρ limit px with red|cheap
    · have price := axis (b+1) (by omega) (by omega) red;omega
    · have up := physical_dominates_basic G K n m hn hm pn pm ht esc d data (b+1) (by omega)
      change 2*C (b+1)≤basicCapacity G K n m r (b+1)+2*ρ at cheap
      change basicCapacity G K n m r (b+1)≤Q (b+1) at up;omega
  have high (j:ℕ) (lo:b+2≤j) (hi:j≤D) : 2*C j+P≤Q j+2*f j :=
    axis j (by omega) hi (full_upper_pure_only hs ht n m hn hm pn pm opp top live large budget j lo hi)
  have balance := seven_high_payment D b μ P ρ h d t r a X₀ q deg gap seven width (by omega) qeq endpoint
  have total := sum_high_endpoint_prices D b P ρ h d X₀ q C Q f large sub low axes border high
    (large_threshold_sum n (D-2)) balance
  have raw := strict_two_interior_inventories G K n m hs ht hn hm pn pm (by clear * - deg;omega) cap top d rank strict
  have inv := joint_physical_sum G K
  change (∑z∈Finset.range (D-1),Q (z+2))=_ at inv
  rw [inv] at total
  change 2*interiorArea n m r D+2*h+2*d≤(D-1)*(a+2*μ)+interiorInventory (G.induce K.rest) D+
    interiorInventory (eraseInternal G K.core) D+D*ρ at total
  change (D-1)*(a+2*μ)+D*ρ+(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest+
    interiorInventory (G.induce K.rest) D+interiorInventory (eraseInternal G K.core) D<2*interiorArea n m r D+2*h+2*d at raw
  clear * - raw total;omega

#print axioms seven_high_full_impossible
end JSP452Audit.StarHost