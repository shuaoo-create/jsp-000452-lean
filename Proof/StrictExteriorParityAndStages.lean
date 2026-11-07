import EndpointStageThresholdCount
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_exterior_parity_and_stages (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (U : Set F.X) (closed : ∀v∈U,∀w,F.G.Adj v w → w∈U)
    (full : ∀v∈U,Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1) :
    let P := matchingEdges (F.G.induce U)
    let O := F.G.induce Uᶜ
    let d := F.rank-matchingEdges F.G
    P+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t ∧ P+F.r+2*(d+∑j,(F.m j-1)/2)≤F.s ∧
    (∀(T:Set ↥(Uᶜ : Set F.X)) (p:ℕ), (∀v:↥(Tᶜ : Set ↥(Uᶜ : Set F.X)), Nat.card ((O.induce Tᶜ).neighborSet v)≤p) →
      (0<originalThresholdCount F.n (p+1) → F.t-F.r-P-1+originalThresholdCount F.n (p+1)≤T.ncard) ∧
      (0<originalThresholdCount F.m (p+1) → F.s-F.r-P-1+originalThresholdCount F.m (p+1)≤T.ncard)) := by
  intro P O d
  let q := F.t-F.r-P
  let k := F.s-F.r-P
  obtain ⟨lq,lk,aq,ak,red,blue⟩ := strict_closed_union_endpoint_pair F paid U closed full
  change d+1≤q at lq
  change d+1≤k at lk
  change matchingEdges O+d+1=F.s+q at aq
  change matchingEdges O+d+1=F.t+k at ak
  have pos : 0<d := by have less := (minimal_rank_exact_source F paid).2.2.1;dsimp [d];omega
  have lens := (strict_closed_union_lengths F paid U closed full).1
  change P+F.r+d+1≤min F.s F.t at lens
  have ls := lens.trans (Nat.min_le_left _ _)
  have lt := lens.trans (Nat.min_le_right _ _)
  have costN := endpoint_forest_parity_cost O F.n F.pn red pos (by omega : 0<q) (by omega) aq
  have costM := endpoint_forest_parity_cost O F.m F.pm blue pos (by omega : 0<k) (by omega) ak
  refine ⟨?_,?_,?_⟩
  · change 2*(d+∑i,(F.n i-1)/2)≤F.t-F.r-P at costN;clear * - costN lt;omega
  · change 2*(d+∑j,(F.m j-1)/2)≤F.s-F.r-P at costM;clear * - costM ls;omega
  · intro T p cap
    exact ⟨endpoint_threshold_stage O F.n F.pn red (by omega : 0<q) T cap,
      endpoint_threshold_stage O F.m F.pm blue (by omega : 0<k) T cap⟩

#print axioms strict_exterior_parity_and_stages
end JSP452Audit.StarHost
