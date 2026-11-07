import CompleteErasedCoreSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def BothActualSuccessors {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d E : ℕ) : Prop :=
  let H := G.induce K.core
  let B := G.induce K.rest
  let Z := eraseInternal G K.core
  let μ := matchingEdges H
  let a := K.roots.ncard
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  let EB := rowEnergy (W.entries n) m (r+a)
  let EZ := rowEnergy J m r
  CompleteExteriorData G K n m r N d ∧
    ForcingRow Z W.len t (padDemand J) (padDemand m) r ∧
    rowCount W.len t r=matchingEdges Z+d+(μ-W.loss) ∧
    rowCount W.len t r+W.loss=N ∧ 0<rowCount W.len t r ∧ rowCount W.len t r<N ∧
    EZ≤Z.edgeSet.ncard ∧ max (EB+(G.edgeSet.ncard-B.edgeSet.ncard)) (EZ+H.edgeSet.ncard)<E

private theorem joint_from_exterior {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d E : ℕ)
    (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (paid : AllSmallerPaid.{u} N) (strict : G.edgeSet.ncard<E) (esc : matchingEdges (G.induce K.core)<s)
    (balance : matchingEdges G+d=N) (pos : 0<d) (ext : CompleteExteriorData G K n m r N d) :
    BothActualSuccessors G K n m r N d E := by
  let H := G.induce K.core
  let B := G.induce K.rest
  let Z := eraseInternal G K.core
  let a := K.roots.ncard
  let μ := matchingEdges H
  let k := matchingEdges B
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  have data := ext
  obtain ⟨one,hi,_,base,_,_,_,eb⟩ := ext
  change 1≤W.loss at one
  change W.loss≤μ at hi
  change rowCount W.len t (r+a)=k+d+(μ-W.loss) at base
  have size : 0<W.len := by change μ<s at esc;dsimp only [RemovalBudget.len];omega
  have real := complete_erased_core_row G K W n m hn pn (component_budget_admits H n pn) row
  have rankZ := whole_core_erasure_exact_rank G K
  change matchingEdges Z=a+k at rankZ
  have sep := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at sep
  have rank : rowCount W.len t r=matchingEdges Z+d+(μ-W.loss) := by dsimp [rowCount] at base ⊢;omega
  have orig : rowCount W.len t r+W.loss=N := by omega
  have positive : 0<rowCount W.len t r := by omega
  have less : rowCount W.len t r<N := by omega
  have price := paid size ht J m (common_erased_antitone n hn W a μ) hm (common_erased_positive n W a μ) pm Z r real less
  have fee := erase_internal_edge_count G K.core
  have feeB := erase_internal_edge_count G K.rest
  change G.edgeSet.ncard=Z.edgeSet.ncard+H.edgeSet.ncard at fee
  change G.edgeSet.ncard=_+B.edgeSet.ncard at feeB
  change rowEnergy (W.entries n) m (r+a)≤B.edgeSet.ncard at eb
  refine ⟨data,real,rank,orig,positive,less,price,?_⟩
  change max (rowEnergy (W.entries n) m (r+a)+(G.edgeSet.ncard-B.edgeSet.ncard)) (rowEnergy J m r+H.edgeSet.ncard)<E
  omega

theorem strict_common_actual_successors (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    let E := rowEnergy F.n F.m F.r
    (μ<F.s → BothActualSuccessors F.G K F.n F.m F.r F.rank d E) ∧
    (μ<F.t → BothActualSuccessors F.G K F.m F.n F.r F.rank d E) := by
  intro μ d E
  obtain ⟨r,b⟩ := strict_both_complete_exteriors F paid K
  have pos : 2≤d := (minimal_strict_source_deficit F paid).2.2
  have orig : matchingEdges F.G+d=F.rank := by have := (minimal_rank_exact_source F paid).2.2.1;dsimp [d];omega
  refine ⟨fun red => joint_from_exterior F.G K F.n F.m F.r F.rank d E F.ht F.hn F.hm F.pn F.pm F.row
    paid F.strict red orig (by omega) (r red),?_⟩
  intro blue
  exact joint_from_exterior F.G K F.m F.n F.r F.rank d E F.hs F.hm F.hn F.pm F.pn
    (swap_positive_forcing_row F.G _ _ F.row) paid F.strict blue orig (by omega) (b blue)

#print axioms strict_common_actual_successors
end JSP452Audit.StarHost
