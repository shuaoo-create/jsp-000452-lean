import PositiveRankAndTheOriginalHeadDegreeInventoryOnTheRegularExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem regular_block_projected_prices (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let D := 2*p
    let W := widthAt F.n F.m F.r
    let O := B.outside
    let N := Nat.card B.piece.supp
    let b := peakCountAbove O (D-1)
    let c := peakCountAbove O (D-2)
    let f := peakCountAbove O (D-3)
    W D≤b+B.P+p-3 ∧ W D≤b+N/5+p-2 ∧ W D≤c+N/5 ∧
      ((W (D-1)≤c+N/4+p+2 ∧ W (D-1)≤f+N/4) ∨ W (D-1)≤N/4+N/7) := by
  intro D W O N b c f
  have many : 6≤p := by have d := strict_source_degree_at_least_eleven F paid;omega
  have large : 12≤D := by dsimp only [D];omega
  obtain ⟨first,second,upper⟩ := regular_block_second_stage F paid B degree head one
  obtain ⟨_,top,mid,_⟩ := regular_third_gap_block_widths F paid p B degree head one
  have costs : W D≤b+N/5+p-2 ∧ W D≤c+N/5 := by
    by_cases live:0<W D
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<D by omega) live
      have w : WinsHeight F.n F.m F.r D x y := win
      obtain ⟨high,typed⟩ := top x y w
      change ExactTypedWidth O x y (W D-N/5) at typed
      let U := peakPrefix O b
      obtain ⟨sz,lo⟩ := exact_peak_inventory_cut O (D-1)
      change U.ncard=b at sz
      have next := typed_width_after_deletion O U w.1 w.2.1 typed
      rw [sz] at next
      have upper : W D-N/5-b≤p-2 := by
        by_cases paidW:0<W D-N/5-b
        · have ht := w.2.2.1
          have need := true_odd_cap_extra_width (O.induce Uᶜ) (D-1) x y (W D-N/5-b) (by dsimp only [D];omega)
            (by omega) (by omega) (by omega) lo next paidW
          change minimumExposure (O.induce Uᶜ) (D-1)≤p at first;omega
        · omega
      obtain ⟨cnt,low⟩ := exact_peak_inventory_cut O (D-2)
      have hh := w.2.2.1
      have lower := typed_inventory_on_actual_cut O w.1 w.2.1 (by omega : x+y-1=(D-1)+1) (by omega) typed _
        (fun z => (low z).trans_lt (by omega))
      rw [cnt] at lower;change W D-N/5≤c at lower;omega
    · omega
  refine ⟨upper,costs.1,costs.2,?_⟩
  by_cases live:0<W (D-1)
  · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<D-1 by omega) live
    have w : WinsHeight F.n F.m F.r (D-1) x y := win
    rcases (mid x y w).2.1 with typed|done'
    · left
      change ExactTypedWidth O x y (W (D-1)-N/4) at typed
      let T := peakPrefix O c
      obtain ⟨sz,lo⟩ := exact_peak_inventory_cut O (D-2)
      change T.ncard=c at sz
      have next := typed_width_after_deletion O T w.1 w.2.1 typed
      rw [sz] at next
      have ht := w.2.2.1
      have charge := typed_width_exposure_at_cap (O.induce Tᶜ) (D-2) x y (W (D-1)-N/4-c) (by omega) lo w.1 w.2.1 (by omega) next
      change minimumExposure (O.induce Tᶜ) (D-2)≤p+2 at second
      obtain ⟨cnt,low⟩ := exact_peak_inventory_cut O (D-3)
      have lower := typed_inventory_on_actual_cut O w.1 w.2.1 (by omega : x+y-1=(D-2)+1) (by omega) typed _
        (fun z => (low z).trans_lt (by omega))
      rw [cnt] at lower;change W (D-1)-N/4≤f at lower
      omega
    · exact Or.inr done'
  · right;omega

#print axioms regular_block_projected_prices
end JSP452Audit.StarHost
