import EveryPossibleFinalDegreeOnTheUniqueRegularExteriorPaysTheMenu
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_block_gap_three_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) : False := by
  let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
  let W := widthAt F.n F.m F.r
  let O := B.outside
  let P := B.P
  let N := Nat.card B.piece.supp
  let i := P-(F.r+1)
  let g := (O.induce (peakPrefix O i)ᶜ).edgeSet.ncard-rowEnergy F.n F.m (F.r+i+P)
  let C := peakCountAbove O
  change H+3=2*p at head
  have many : 6≤p := by have bound := strict_source_degree_at_least_eleven F paid;omega
  have fee := regular_third_three_columns F paid B degree head one
  have rates := regular_block_projected_prices F paid B degree head one
  change W (2*p)≤C (2*p-1)+P+p-3 ∧ W (2*p)≤C (2*p-1)+N/5+p-2 ∧ W (2*p)≤C (2*p-2)+N/5 ∧
    ((W (2*p-1)≤C (2*p-2)+N/4+p+2 ∧ W (2*p-1)≤C (2*p-3)+N/4) ∨ W (2*p-1)≤N/4+N/7) at rates
  rw [show 2*p-1=H+2 by omega,show 2*p-2=H+1 by omega,show 2*p-3=H by omega,←head] at rates
  obtain ⟨r1,r2,r3,rm⟩ := rates
  have last := regular_lowest_stage_platform F paid B degree head one
  have Ppos : 0<P := lt_of_lt_of_le (by omega : 0<p) B.original_geometry.1
  exact regular_third_price_false P p N i (C (H+2)) (C (H+1)) (C H) g (W (H+1)) (W (H+2)) (W (H+3))
    B.original_geometry.2.1 many B.original_geometry.1 (by dsimp only [i];omega)
    ⟨peak_counts_antitone _ (by omega),peak_counts_antitone _ (by omega)⟩ fee ⟨r1,r2,r3⟩ rm last

theorem strict_original_head_gap_at_most_two (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D-H≤2 := by
  intro D H
  have cap := strict_original_head_gap_at_most_three F paid
  change D-H≤3 at cap
  by_contra! large
  have gap : D=H+3 := by omega
  obtain ⟨even,one,_,J,odd,reg,_⟩ := third_gap_requires_original_regular_component F paid gap
  let p := D/2
  have degree : D=2*p := by change D%2=0 at even;dsimp only [p];omega
  have block : RegularOddBlock F.G p := ⟨J,odd,fun v hv => (reg v hv).trans degree⟩
  exact regular_block_gap_three_impossible F paid block degree (gap.symm.trans degree) one

#print axioms regular_block_gap_three_impossible
#print axioms strict_original_head_gap_at_most_two
end JSP452Audit.StarHost
