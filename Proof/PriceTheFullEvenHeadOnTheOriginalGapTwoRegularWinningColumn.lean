import BothSurvivingColumnsPayForTheSameRegularExteriorCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_gap_two_projected_prices (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+2=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let D := 2*p
    let W := widthAt F.n F.m F.r
    let O := B.outside
    let N := Nat.card B.piece.supp
    let b := peakCountAbove O (D-1)
    let c := peakCountAbove O (D-2)
    W D≤b+B.P+p-3 ∧ W D+p+1≤b+2*B.P ∧
      (W D≤b+N/4 ∨ W D≤b+N/5+p-2) ∧
      (W (D-1)≤c+N/3+p+2 ∨ W (D-1)≤N/3+N/7) := by
  intro D W O N b c
  have many : 6≤p := by have d := strict_source_degree_at_least_eleven F paid;omega
  obtain ⟨first,second,upper,size⟩ := regular_gap_two_second_stage F paid B degree head one
  obtain ⟨_,top,mid⟩ := regular_second_gap_block_widths F paid p B degree head one
  refine ⟨upper,size,?_,?_⟩
  · by_cases live:0<W D
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<D by dsimp only [D];omega) live
      have w : WinsHeight F.n F.m F.r D x y := win
      obtain ⟨mi,typed⟩ := top x y w
      let M := N/(min x y+1)
      change ExactTypedWidth O x y (W D-M) at typed
      let U := peakPrefix O b
      obtain ⟨sz,lo⟩ := exact_peak_inventory_cut O (D-1)
      change U.ncard=b at sz
      have next := typed_width_after_deletion O U w.1 w.2.1 typed
      rw [sz] at next
      have ht := w.2.2.1
      change minimumExposure (O.induce Uᶜ) (D-1)≤p at first
      have price : M≤N/4 := Nat.div_le_div_left (by omega) (by decide)
      by_cases pos:0<W D-M-b
      · have need := full_even_head_exposure_at_odd_cap (O.induce Uᶜ) (D-1) x y (W D-M-b) (by dsimp only [D];omega)
          (by omega) (by omega) (by dsimp only [D] at ht ⊢;omega) lo next pos
        have four : 4≤min x y := by
          by_contra! no
          dsimp only [D] at ht
          split_ifs at need <;> omega
        have small : M≤N/5 := Nat.div_le_div_left (by omega) (by decide)
        right;split_ifs at need <;> omega
      · left;omega
    · left;omega
  · by_cases live:0<W (D-1)
    · obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<D-1 by dsimp only [D];omega) live
      have w : WinsHeight F.n F.m F.r (D-1) x y := win
      rcases (mid x y w).2 with typed|dead
      · left
        change ExactTypedWidth O x y (W (D-1)-N/3) at typed
        let T := peakPrefix O c
        obtain ⟨sz,lo⟩ := exact_peak_inventory_cut O (D-2)
        change T.ncard=c at sz
        have next := typed_width_after_deletion O T w.1 w.2.1 typed
        rw [sz] at next
        have ht := w.2.2.1
        have charge := typed_width_exposure_at_cap (O.induce Tᶜ) (D-2) x y (W (D-1)-N/3-c) (by dsimp only [D];omega) lo w.1 w.2.1 (by dsimp only [D] at ht ⊢;omega) next
        change minimumExposure (O.induce Tᶜ) (D-2)≤p+2 at second
        omega
      · exact Or.inr dead
    · left;omega

#print axioms regular_gap_two_projected_prices
end JSP452Audit.StarHost