import TheUnequalEvenFactorObstructionRetainsActualIsolatedOddComponents
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D} {P:ScaledPortPlan K k c}

theorem PortGraphLayers.every_odd_regular_component_misses (E:PortGraphLayers P) (t:Fin k) :
    (oddRegularComponents G D).ncard≤(E.missing t).ncard := by
  classical
  let H := E.graph t
  let U := E.missing t
  let J := oddRegularComponents G D
  have spot (Q:↥J) : ∃v,v∈Q.val.supp ∧ v∈U := by
    have cap (v) (hv:v∈Q.val.supp) : Nat.card (G.neighborSet v)=D := Q.property.2 v hv
    have cost := layer_degree_on_full_set H U Q.val.supp (E.full t) cap
    have hand := JSP452Audit.StarHost.two_block_handshake H Q.val.supp
    have zero : crossCount H Q.val.supp Q.val.suppᶜ=0 := by
      apply crossCount_of_no_edges;intro x hx y hy edge
      exact hy ((Q.val.mem_supp_congr_adj (E.sub t edge)).mp hx)
    rw [zero,Nat.add_zero] at hand
    have odd := Q.property.1
    change Odd (Nat.card Q.val.supp) at odd
    rw [Nat.card_coe_set_eq,Nat.odd_iff] at odd
    have pos : 0<(Q.val.supp∩U).ncard := by omega
    obtain ⟨v,a,b⟩ := (Set.ncard_pos (Set.toFinite _)).mp pos
    exact ⟨v,a,b⟩
  choose x own missing using spot
  let f (Q:↥J) : ↥U := ⟨x Q,missing Q⟩
  have inj : Function.Injective f := by
    intro Q W eq
    have same:x Q=x W := congrArg (fun z:↥U => z.val) eq
    exact Subtype.ext (ConnectedComponent.eq_of_common_vertex (own Q) (same.symm ▸ own W))
  exact Nat.card_le_card_of_injective f inj

namespace ScaledPortPlan
variable (P:ScaledPortPlan K k c)
abbrev wholeFamily := Subtype.val '' P.family
abbrev cutRoots := regionRoots G K.barrier P.wholeFamily
abbrev cutCore := regionCore G K.barrier P.wholeFamily
abbrev cutRest := regionRest G K.barrier P.wholeFamily
noncomputable abbrev excess := P.family.ncard-P.cutRoots.ncard
noncomputable abbrev shortfall := rootShortfall G P.cutRoots D

theorem exact_excess (E:PortGraphLayers P) :
    P.family.ncard=P.cutRoots.ncard+P.excess ∧
    k*P.excess=c*P.shortfall+∑t:Fin k,(E.missing t).ncard := by
  obtain ⟨f,_⟩ := P.assignedRoots
  have room : P.cutRoots.ncard≤P.family.ncard := Nat.card_le_card_of_injective f f.injective
  have sum := E.true_total_misses
  change k*P.family.ncard=k*P.cutRoots.ncard+c*P.shortfall+_ at sum
  have exact : P.family.ncard=P.cutRoots.ncard+P.excess := by dsimp only [excess];omega
  rw [exact,Nat.mul_add] at sum;exact ⟨exact,by omega⟩

theorem includes_odd_regular_excess (live:0<k) (E:PortGraphLayers P) :
    (oddRegularComponents G D).ncard≤P.excess := by
  have sum := Finset.sum_le_sum (s:=(Finset.univ:Finset (Fin k))) (fun t _ => E.every_odd_regular_component_misses t)
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at sum
  have trueFee := (P.exact_excess E).2
  exact Nat.le_of_mul_le_mul_left (show k*(oddRegularComponents G D).ncard≤k*P.excess by omega) live

#print axioms exact_excess
#print axioms includes_odd_regular_excess
end ScaledPortPlan
#print axioms PortGraphLayers.every_odd_regular_component_misses
end JSP452Audit.StarHost
