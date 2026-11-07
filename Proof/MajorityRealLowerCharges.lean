import MajorityActualColumnShape
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem majority_real_low_caps {s t r D b : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (head : n ⟨0,hs⟩=D) (blue : m ⟨0,ht⟩=b) (large : 3≤b) (sub : b<D)
    (top : diagonal n m (r+2)=D+1) (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (esc : matchingEdges (G.induce K.core)<s) (d : ℕ) (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t) (space : matchingEdges (G.induce K.core)+originalThresholdCount m 2≤s)
    (inner : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1) (width : highestWidth n m r<d) (v : ℕ)
    (lo : 3≤v) (hi : v≤b) :
    let q := matchingEdges (G.induce K.core)+1-t
    let C := widthAt n m r
    let Q := jointPhysicalInventory G K
    2*C v≤Q v+2*q ∧ (D-b+2≤v → 2*C v≤Q v) := by
  intro q C Q
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let U := uniformEnvelope (G.induce K.rest)
  let Z := uniformEnvelope (eraseInternal G K.core)
  change t+d+2*(_ : ℕ)≤μ+1 at inner
  have cap := full_head_interior_prefix_cap hs ht n m hn hm head blue top (by omega : D+2-b≤D) (by omega)
  have present := actual_height_positive n m live top v (by omega)
  have either := active_opposite_pure_or_paid G K n m hs ht hn hm pn pm budget space esc v lo (hi.trans_eq blue.symm) present
  have base : Q v=a+2*μ+U v+Z v := rfl
  rcases either with axis|cheap
  · have fits : t+∑j,(m j-1)/2≤μ := by omega
    have repair := even_cut_both_envelopes G K n m hn hm pn pm ht row fits v (by omega)
    change originalThresholdCount n v≤U v+2*q+r+a ∧ originalThresholdCount n v≤Z v+2*q+r at repair
    have eq : q+t=μ+1 := by dsimp [q];omega
    change C v≤originalThresholdCount n v+t-1-r at axis
    constructor
    · omega
    · intro high
      have ord := threshold_anti_height n (show D+2-b≤v by omega)
      omega
  · have paid := cheap.trans (physical_dominates_basic G K n m hn hm pn pm ht esc d data v (by omega))
    change 2*C v≤Q v at paid
    exact ⟨by omega,fun _ => paid⟩

#print axioms majority_real_low_caps
end JSP452Audit.StarHost