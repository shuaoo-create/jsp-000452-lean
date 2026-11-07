import StrictCommonActualSuccessors
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Sum of the two actual deletion fees; each is taken on its own
original subgraph. The root shortfall cancels exactly. -/
theorem sum_actual_successor_fees {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (K : DegreeRegion G D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) :
    let a := K.roots.ncard
    let μ := matchingEdges (G.induce K.core)
    (G.edgeSet.ncard-(G.induce K.rest).edgeSet.ncard)+(G.induce K.core).edgeSet.ncard =
      D*(a+2*μ)+D*minimumExposure G D+(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest := by
  intro a μ
  obtain ⟨cover,apart,sep⟩ := core_rest_partition G K.barrier K.pieces
  let iso := regionSumIso G K.rootsᶜ K.core K.rest cover apart (fun _ hc _ hb => sep hc hb)
  have split : (G.induce K.rootsᶜ).edgeSet.ncard=(G.induce K.core).edgeSet.ncard+(G.induce K.rest).edgeSet.ncard := by
    rw [←edge_ncard_sumGraph];exact (Nat.card_congr iso.mapEdgeSet).symm
  have del := root_deletion_cost_with_slack G K.roots D (fun x _ => cap x)
  change G.edgeSet.ncard+rootShortfall G K.roots D+(G.induce K.roots).edgeSet.ncard=
    (G.induce K.rootsᶜ).edgeSet.ncard+D*a at del
  rw [split] at del
  have fee := ordinary_region_original_edge_account G D cap K
  change 2*G.edgeSet.ncard+rootShortfall G K.roots D=2*D*(a+μ)+D*minimumExposure G D+
    crossCount G K.roots K.rest+2*(G.induce K.rest).edgeSet.ncard at fee
  rw [show 2*D*(a+μ)=2*(D*a)+2*(D*μ) by ring] at fee
  rw [show D*(a+2*μ)=D*a+2*(D*μ) by ring]
  have seen := erase_internal_edge_count G K.rest
  omega

def JointAreaDeficit {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r E : ℕ) : Prop :=
  let H := G.induce K.core
  let μ := matchingEdges H
  let W := componentBudget H n
  let a := K.roots.ncard
  let J := commonErasedDemand n W a μ
  D*(a+2*μ)+D*minimumExposure G D+(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest+
    rowEnergy (W.entries n) m (r+a)+rowEnergy J m r < 2*E

theorem joint_rows_strict_area {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d E : ℕ)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (data : BothActualSuccessors G K n m r N d E) :
    JointAreaDeficit G K n m r E := by
  have sides := data.2.2.2.2.2.2.2
  have fees := sum_actual_successor_fees G D K cap
  dsimp only [JointAreaDeficit]
  rw [←fees]
  rcases max_lt_iff.mp sides with ⟨b,z⟩
  omega

theorem strict_common_successor_area (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let E := rowEnergy F.n F.m F.r
    (μ<F.s → JointAreaDeficit F.G K F.n F.m F.r E) ∧
    (μ<F.t → JointAreaDeficit F.G K F.m F.n F.r E) := by
  intro μ E
  obtain ⟨red,blue⟩ := strict_common_actual_successors F paid K
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  exact ⟨fun esc => joint_rows_strict_area _ _ _ _ _ _ _ _ cap (red esc),
    fun esc => joint_rows_strict_area _ _ _ _ _ _ _ _ cap (blue esc)⟩

#print axioms sum_actual_successor_fees
#print axioms joint_rows_strict_area
#print axioms strict_common_successor_area
end JSP452Audit.StarHost
