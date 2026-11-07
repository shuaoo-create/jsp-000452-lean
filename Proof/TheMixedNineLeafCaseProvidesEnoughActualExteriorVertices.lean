import NineLeafHeadsSaveOneActualNonunitColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_nine_head_mixed_support_stock (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (narrow:highestWidth F.n F.m F.r≤2) (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (head:0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9)
    (j a b:ℕ) (lo:2≤j) (hi:j≤9) (na:2≤a) (mb:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    W.half<2*(F.rank-W.rank-matchingEdges W.outside) := by
  let M := W.slotDamage 2
  let P := W.half
  let tax (i:ℕ) := if i=j then M else P
  let E := uniformEnvelope W.outside
  let L := widthAt F.n F.m F.r
  have pos := (strict_ten_inventory F paid ten).1
  have savings := ten_port_nine_head_mixed_savings F paid ten W narrow deep length head j a b lo hi na mb win
  have each (i:ℕ) : L (i+2)≤E (i+2)+tax (i+2) := by
    by_cases same:i+2=j
    · simpa only [tax,same,if_pos rfl] using (show L j≤E j+tax j from by simpa [tax] using savings)
    · simpa only [tax,if_neg same] using ten_port_every_lower_column W pos F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
        (by omega) (by omega) F.row (i+2) (by omega)
  have sum := Finset.sum_le_sum (s:=Finset.range 8) (fun i _ => each i)
  rw [Finset.sum_add_distrib] at sum
  have taxsum : (∑i∈Finset.range 8,tax (i+2))=7*P+M := by
    dsimp only [tax];interval_cases j <;> simp [Finset.sum_range_succ] <;> omega
  rw [taxsum] at sum
  have slots := W.port_slot_sizes pos
  have size : 3*M≤2*P+W.parity+2*W.portCount := slots.1
  have small : M≤P := by have := slots.2.2.2;omega
  have book := W.size_and_fee pos
  have parity := book.2.2.1
  have lower : 22≤P := book.2.2.2.2.2.1
  have ports := book.2.1
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have volume := ten_port_paid_volume F paid ten W 2 (P-M)
    (fun i => by have cap := red i;rw [ten] at cap;omega)
    (fun i => by have cap := blue i;rw [ten] at cap;omega) deep length (by
      change (∑i∈Finset.range 8,L (i+2))+(P-M)≤(∑i∈Finset.range 8,E (i+2))+8*P;omega)
  change P+_+5*W.parity+W.portCount+1+(P-M)+_≤_+M+2*highestWidth F.n F.m F.r at volume
  omega

#print axioms ten_nine_head_mixed_support_stock
end JSP452Audit.StarHost
