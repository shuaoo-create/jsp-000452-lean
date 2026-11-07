import TheMatchingAccountOnTheIdenticalTenDegreeExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_paid_volume (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r)) (z extra:ℕ)
    (rn:∀i,F.n i+z≤11) (bm:∀j,F.m j+z≤11)
    (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (low:(∑i∈Finset.range 8,widthAt F.n F.m F.r (i+2))+extra≤
      (∑i∈Finset.range 8,uniformEnvelope W.outside (i+2))+8*W.half) :
    W.half+(W.half-W.rank)+5*W.parity+W.portCount+1+extra+envelopeReserve W.outside 9≤
      F.rank-W.rank-matchingEdges W.outside+W.slotDamage z+2*highestWidth F.n F.m F.r := by
  have fee := ten_port_matching_account F paid ten W z extra rn bm deep length low
  have book := W.size_and_fee (strict_ten_inventory F paid ten).1
  omega

theorem ten_port_volume_two_three (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t) :
    let h := highestWidth F.n F.m F.r
    let d := F.rank-W.rank-matchingEdges W.outside
    let j := W.half-W.rank
    W.half+3*j+14*W.parity+W.portCount+3≤3*d+6*h ∧
      ((∀i,F.n i≤8) → (∀i,F.m i≤8) →
        2*W.half+4*j+19*W.parity+W.portCount+4≤4*d+8*h) := by
  intro h d j
  have pos := (strict_ten_inventory F paid ten).1
  have budgets := W.port_slot_sizes pos
  have row := ten_port_lower_sum F W pos (by omega) (by omega)
  have heads := strict_only_double_escape F paid
  have red (i) : F.n i+2≤11 := by have q := heads.1 i;rw [ten] at q;omega
  have blue (i) : F.m i+2≤11 := by have q := heads.2.1 i;rw [ten] at q;omega
  have low := ten_port_paid_volume F paid ten W 2 0 red blue deep length (by simpa using row)
  change W.half+j+5*W.parity+W.portCount+1+0+_≤d+W.slotDamage 2+2*h at low
  constructor
  · omega
  · intro left right
    have high := ten_port_paid_volume F paid ten W 3 0 (fun i => by have := left i;omega) (fun i => by have := right i;omega)
      deep length (by simpa using row)
    change W.half+j+5*W.parity+W.portCount+1+0+_≤d+W.slotDamage 3+2*h at high
    omega

#print axioms ten_port_paid_volume
#print axioms ten_port_volume_two_three
end JSP452Audit.StarHost
