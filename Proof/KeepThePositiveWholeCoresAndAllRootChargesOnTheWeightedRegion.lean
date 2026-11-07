import EachActualLayerMissesAVertexInEveryOriginalOddRegularComponent
namespace JSP452Audit.StarHost.ScaledPortPlan
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D} (P:ScaledPortPlan K k c)
abbrev positives := positivePieces G K.barrier P.wholeFamily D
abbrev paidCore := regionCore G K.barrier P.positives
noncomputable abbrev capacity := matchingEdges (G.induce P.paidCore)
noncomputable abbrev weight := edgeSurplus (G.induce P.paidCore) D
noncomputable abbrev beta := crossCount G P.cutRoots P.cutRest
noncomputable abbrev gamma (h:ℕ) : ℤ := (P.shortfall:ℤ)+(G.induce P.cutRoots).edgeSet.ncard+h-P.weight

theorem exact_weight_and_root_cost (E:PortGraphLayers P) (cap:∀x,Nat.card (G.neighborSet x)≤D) (h:ℕ) :
    2*edgeSurplus (G.induce P.cutCore) D=(D:ℤ)*P.excess+P.shortfall+2*(G.induce P.cutRoots).edgeSet.ncard+P.beta ∧
    2*P.gamma h+(D:ℤ)*P.excess+P.beta≤(P.shortfall:ℤ)+2*h ∧
    2*P.weight≤(D:ℤ)*P.positives.ncard ∧ (D:ℤ)*P.positives.ncard≤2*P.capacity ∧ P.weight≤P.capacity ∧
    P.paidCore.ncard=2*P.capacity+P.positives.ncard := by
  obtain ⟨full,sep,order,rank⟩ := P.true_rank_and_degree
  have split := (P.exact_excess E).1
  change P.cutCore.ncard=2*matchingEdges (G.induce P.cutCore)+P.family.ncard at order
  rw [split,←Nat.add_assoc] at order
  obtain ⟨ac,ab,cb,all⟩ := region_partition G K.barrier P.wholeFamily
  have exact := weight_handshake G P.cutRoots P.cutCore P.cutRest D P.excess (fun v _ => cap v) full ac ab cb all sep order
  change 2*edgeSurplus (G.induce P.cutCore) D=(D:ℤ)*P.excess+P.shortfall+2*(G.induce P.cutRoots).edgeSet.ncard+P.beta at exact
  have saved := positivePieces_dominate G K.barrier P.wholeFamily D
  change edgeSurplus (G.induce P.cutCore) D≤P.weight at saved
  obtain ⟨a,b,c⟩ := positive_selection_caps G K.barrier K.tight P.wholeFamily D (fun Q _ => (K.critical Q).1)
    (fun Q _ => (K.critical Q).2) (fun Q _ x => (induced_neighbor_count_le (G.induce K.barrierᶜ) Q.supp x).trans
      ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap x.val.val)))
  have size := core_order_matching G K.barrier K.tight P.positives (fun Q _ => (K.critical Q).1)
  exact ⟨exact,by dsimp only [gamma];omega,a,b,c,size⟩

#print axioms exact_weight_and_root_cost
end JSP452Audit.StarHost.ScaledPortPlan
