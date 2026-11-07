import CubicEscapePriceArithmetic
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Both size alternatives are paid by rows on this very exterior.
No rank induction or graph assignment is transferred between hosts. -/
theorem cubic_actual_escape_paid {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D) (three : D=3)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (top : diagonal n m (r+2)=4) (head : n ⟨0,hs⟩=3) (mcap : m ⟨0,ht⟩≤2)
    (over : originalThresholdCount n 3+t<originalThresholdCount n 2+originalThresholdCount m 2)
    (paid : AllSmallerPaid.{u} (rowCount s t r)) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (tail : 3≤s-matchingEdges (G.induce K.core))
    (rank : rowCount s t r=rowCount (s-matchingEdges (G.induce K.core)) t (r+K.roots.ncard)+
      (K.roots.ncard+matchingEdges (G.induce K.core)))
    (smaller : rowCount (s-matchingEdges (G.induce K.core)) t (r+K.roots.ncard)<rowCount s t r)
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (lim : minimumExposure G D≤2)
    (root : 3*minimumExposure G D+rootShortfall G K.roots D≤2*highestWidth n m r+2) :
    rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let S := s-μ
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let P := originalThresholdCount n 3
  let H := G.induce K.rest
  have len : s=S+μ := by change 3≤s-μ at tail;dsimp [S];omega
  change 3≤S at tail
  change rowCount s t r=rowCount S t (r+a)+(a+μ) at rank
  change rowCount S t (r+a)<rowCount s t r at smaller
  have edge := ordinary_region_original_edge_account G 3 cap K
  change 2*G.edgeSet.ncard+rootShortfall G K.roots 3=6*(a+μ)+3*minimumExposure G 3+
    crossCount G K.roots K.rest+2*H.edgeSet.ncard at edge
  obtain ⟨Ppos,Bpos,peak⟩ := cubic_binary_peak_width hs ht n m hn hm pn pm head.le mcap live top
  obtain ⟨w,area⟩ := cubic_overrun_profile hs ht n m hn hm pn pm live top mcap over
  have prices (v:Fin S→ℕ) (hv:Antitone v) (pv:∀i,1≤v i)
      (real : ForcingRow H S t (padDemand v) (padDemand m) (r+a)) :
      rowCount S t (r+a)+widthAt v m (r+a) 2+widthAt v m (r+a) 3≤H.edgeSet.ncard := by
    have price := paid (by omega : 0<S) ht v m hv hm pv pm H (r+a) real smaller
    exact (row_area_three_layers (by omega) ht v m pv pm _).trans price
  have enough (v:Fin S→ℕ) (hv:Antitone v) (pv:∀i,1≤v i)
      (real : ForcingRow H S t (padDemand v) (padDemand m) (r+a))
      (one : 0<originalThresholdCount v 2) (fit : A≤μ+originalThresholdCount v 2) :
      rowEnergy n m r≤G.edgeSet.ncard := by
    obtain ⟨blue,other⟩ := exterior_binary_layer_bounds (by omega) ht v m hv hm pv pm (r+a) Bpos
    obtain ⟨red,mixed⟩ := other one
    exact cubic_binary_witness_pays s t r (rowCount s t r) a μ S A B _ _ _ _ _ _ _ _ _ _ _
      len rank width.1 width.2 root edge area w fit blue red mixed (prices v hv pv real)
  let v := remainingDemand n μ
  have hv := remainingDemand_antitone n hn μ
  have pv := remainingDemand_positive n pn μ
  have real := exterior_complete_red_tail G K n m hn hm pn pm row
  have cnt := threshold_tail_count n hn μ 2
  change originalThresholdCount v 2=A-μ at cnt
  by_cases many : μ<A
  · exact enough v hv pv real (by omega) (by omega)
  by_cases big : K.core.ncard<nonunitOrder n
  · have ext := oversize_binary_exterior G K n m hn hm pn pm row big
    have one : 0<originalThresholdCount (@oneBinaryHead S) 2 := by
      refine (original_threshold_prefix (@oneBinaryHead S) (oneBinaryHead_antitone S) 2 ⟨0,by omega⟩).1 ?_
      simp [oneBinaryHead]
    exact enough _ (oneBinaryHead_antitone S) oneBinaryHead_positive ext one (by omega)
  · have order := cubic_nonunit_order n (fun i => (hn (show (⟨0,hs⟩:Fin s) ≤ i from Nat.zero_le _)).trans head.le)
    have core := K.core_order
    change K.core.ncard=2*μ+a+minimumExposure G 3 at core
    have size : 3*A+P≤2*μ+a+minimumExposure G 3 := by change nonunitOrder n=3*A+P at order;omega
    obtain ⟨blue,_⟩ := exterior_binary_layer_bounds (by omega : 0<S) ht v m hv hm pv pm (r+a) Bpos
    have lower := prices v hv pv real
    exact cubic_small_nonunit_pays s t r (rowCount s t r) a μ S A B P _ _ _ _ _ _ _ _
      len rank tail width.1 width.2 lim root edge area w (by omega) size peak Ppos over (by omega)

#print axioms cubic_actual_escape_paid
end JSP452Audit.StarHost
