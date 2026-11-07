import BothMatchingEndpointsAndTheirParityCostsOnTheSamePortExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_matching_account (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r)) (z extra:ℕ)
    (rn:∀i,F.n i+z≤11) (bm:∀j,F.m j+z≤11)
    (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (low:(∑i∈Finset.range 8,widthAt F.n F.m F.r (i+2))+extra≤
      (∑i∈Finset.range 8,uniformEnvelope W.outside (i+2))+8*W.half) :
    let d := F.rank-W.rank-matchingEdges W.outside
    let h := highestWidth F.n F.m F.r
    W.fee+9*W.rank+extra+envelopeReserve W.outside 9+2≤8*W.half+W.slotDamage z+2*h+d := by
  intro d h
  let L := widthAt F.n F.m F.r
  let C := uniformEnvelope W.outside
  have positive := (strict_ten_inventory F paid ten).1
  have book := W.size_and_fee positive
  have fee : W.piece.edgeSet.ncard=10*W.rank+W.fee := book.2.2.2.2.2.2.2.1
  have split := erase_internal_edge_count F.G W.supportᶜ
  change F.G.edgeSet.ncard=W.piece.edgeSet.ncard+W.outside.edgeSet.ncard at split
  have balance := (ten_port_exterior_matching_endpoints F W deep length).2.1
  change W.rank+matchingEdges W.outside+d=F.rank at balance
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=10) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+(∑i∈Finset.range 9,L (i+2))+h at area
  rw [Finset.sum_range_succ] at area
  have inv := (envelope_reserve_account W.outside 9).1
  change envelopeReserve W.outside 9+(matchingEdges W.outside+(∑i∈Finset.range 9,C (i+2)))=W.outside.edgeSet.ncard at inv
  rw [Finset.sum_range_succ] at inv
  norm_num only [show 8+2=10 by decide] at inv area
  have top := (ten_tenth_column_on_the_actual_exterior F paid ten W z rn bm).1
  change L 10≤C 10+W.slotDamage z+(h-1) at top
  change (∑i∈Finset.range 8,L (i+2))+extra≤(∑i∈Finset.range 8,C (i+2))+8*W.half at low
  change 1≤h at positive
  have strict := F.strict
  omega

theorem ten_port_lower_sum (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ} (W:TenPortSupport F.G K h)
    (positive:1≤h) (ls:W.rank<F.s) (lt:W.rank<F.t) :
    (∑i∈Finset.range 8,widthAt F.n F.m F.r (i+2))≤(∑i∈Finset.range 8,uniformEnvelope W.outside (i+2))+8*W.half := by
  have pay := Finset.sum_le_sum (s:=Finset.range 8) (fun i _ =>
    ten_port_every_lower_column W positive F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm ls lt F.row (i+2) (by omega))
  simpa [Finset.sum_add_distrib] using pay

#print axioms ten_port_matching_account
#print axioms ten_port_lower_sum
end JSP452Audit.StarHost
