import PriceTheFullEvenHeadOnTheOriginalGapTwoRegularWinningColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_second_price_false (P p N i b c g w₀ w₁:ℕ)
    (ord:N=2*P+1) (big:6≤p) (room:p≤P) (short:i<P) (stock:w₁≤c+N/4) (hist:b≤c)
    (fee:g+2*P+p+min i c+min i b≤min (i+P) w₀+min (i+P) w₁)
    (top:w₁≤b+P+p-3 ∧ w₁+p+1≤b+2*P ∧ (w₁≤b+N/4 ∨ w₁≤b+N/5+p-2))
    (mid:w₀≤c+N/3+p+2 ∨ w₀≤N/3+N/7) : False := by
  by_cases full:i ≤ b
  · omega
  by_cases above:i ≤ c
  · omega
  rcases top.2.2 with first|second <;> rcases mid with live|dead <;> omega

theorem regular_block_gap_two_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+2=2*p)
    (one:highestWidth F.n F.m F.r=1) : False := by
  let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
  let W := widthAt F.n F.m F.r
  let O := B.outside
  let P := B.P
  let N := Nat.card B.piece.supp
  let i := P-(F.r+1)
  let g := (O.induce (peakPrefix O i)ᶜ).edgeSet.ncard-rowEnergy F.n F.m (F.r+i+P)
  let C := peakCountAbove O
  change H+2=2*p at head
  have many : 6≤p := by have bound := strict_source_degree_at_least_eleven F paid;omega
  have fee := regular_second_two_columns F paid B degree head one
  have rates := regular_gap_two_projected_prices F paid B degree head one
  change W (2*p)≤C (2*p-1)+P+p-3 ∧ W (2*p)+p+1≤C (2*p-1)+2*P ∧
    (W (2*p)≤C (2*p-1)+N/4 ∨ W (2*p)≤C (2*p-1)+N/5+p-2) ∧
    (W (2*p-1)≤C (2*p-2)+N/3+p+2 ∨ W (2*p-1)≤N/3+N/7) at rates
  rw [show 2*p-1=H+1 by omega,show 2*p-2=H by omega,←head] at rates
  have stock : W (2*p)≤C H+N/4 := by
    by_cases live:0<W (2*p)
    · obtain ⟨x,y,wins⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<2*p by omega) live
      have win : WinsHeight F.n F.m F.r (2*p) x y := wins
      obtain ⟨mi,typed⟩ := (regular_second_gap_block_widths F paid p B degree head one).2.1 x y win
      change ExactTypedWidth O x y (W (2*p)-N/(min x y+1)) at typed
      have cap : N/(min x y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
      obtain ⟨sz,lo⟩ := exact_peak_inventory_cut O H
      have ht := win.2.2.1
      have bill := typed_inventory_on_actual_cut O win.1 win.2.1 (by omega : x+y-1=(2*p-1)+1) (by omega) typed _
        (fun v => (lo v).trans_lt (by omega))
      rw [sz] at bill;change _≤C H at bill;omega
    · omega
  rw [←head] at stock
  have enough : p≤P := B.original_geometry.1
  exact regular_second_price_false P p N i (C (H+1)) (C H) g (W (H+1)) (W (H+2))
    B.original_geometry.2.1 many enough (by dsimp only [i];omega) stock (peak_counts_antitone _ (by omega)) fee
    ⟨rates.1,rates.2.1,rates.2.2.1⟩ rates.2.2.2

theorem strict_original_head_gap_is_one (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D=H+1 := by
  intro D H
  have cap := strict_original_head_gap_at_most_two F paid
  change D-H≤2 at cap
  have pos := (strict_double_head_gap_range F paid).1
  change 1≤D-H at pos
  by_contra! no
  have gap : D=H+2 := by omega
  obtain ⟨even,one,single⟩ := strict_gap_two_has_one_original_odd_regular_component F paid gap
  change (oddRegularComponents F.G D).ncard=1 at single
  obtain ⟨J,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<(oddRegularComponents F.G D).ncard by rw [single];decide)
  let p := D/2
  have degree : D=2*p := by dsimp only [p];omega
  have block : RegularOddBlock F.G p := ⟨J,mem.1,fun v hv => (mem.2 v hv).trans degree⟩
  exact regular_block_gap_two_impossible F paid block degree (gap.symm.trans degree) one

#print axioms regular_second_price_false
#print axioms regular_block_gap_two_impossible
#print axioms strict_original_head_gap_is_one
end JSP452Audit.StarHost