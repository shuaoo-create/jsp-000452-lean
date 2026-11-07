import FullHighAndBoundaryRealColumns
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_low_physical_price {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (esc : matchingEdges (G.induce K.core)<s) (d : ℕ)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (deg : 2≤D) (top : diagonal n m (r+2)=D+1) (before : r<t)
    (room : t+(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core))
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2)
    (blue : 0<originalThresholdCount m 2) :
    2*widthAt n m r 2≤jointPhysicalInventory G K 2+(matchingEdges (G.induce K.core)+1-t) := by
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let W := componentBudget (G.induce K.core) n
  let q := μ+1-t
  let A := originalThresholdCount n 2
  let c := originalThresholdCount (W.entries n) 2
  let U := uniformEnvelope (G.induce K.rest) 2
  let Z := uniformEnvelope (eraseInternal G K.core) 2
  have opts := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by omega))
  rcases opts with red|blueW
  · obtain ⟨fit,redFee,_,_,_⟩ := high_boundary_retained_rectangles G K n m hn hm pn pm ht esc d data nonunit blue blue
    change W.loss≤μ at fit
    obtain ⟨base,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
    change A≤W.loss+c at base
    change c+t-1-(r+a)≤U at redFee
    have zfee := (even_cut_both_envelopes G K n m hn hm pn pm ht row room 2 (by decide)).2
    change A≤Z+2*q+r at zfee
    change t+_≤μ at room
    have qeq : q+t=μ+1 := by dsimp [q];omega
    change widthAt n m r 2=A+t-1-r at red
    change 2*widthAt n m r 2≤a+2*μ+U+Z+q;omega
  · have available := (joint_common_blue_axis G K n m hn hm pn esc r 2 blue).1
    have up := physical_dominates_basic G K n m hn hm pn pm ht esc d data 2 (by decide)
    omega

#print axioms full_low_physical_price
end JSP452Audit.StarHost