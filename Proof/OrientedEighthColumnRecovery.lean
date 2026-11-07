import SeventhColumnOfActualEightRemainder
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem oriented_eight_dead_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (a b M:ℕ) (win:WinsHeight F.n F.m F.r 8 a b)
    (small:originalThresholdCount F.n a≤M) (small':originalThresholdCount F.m b≤M) :
    widthAt F.n F.m F.r 8≤M+(highestWidth F.n F.m F.r-1) := by
  obtain ⟨ap,bp,height,red,blue,eq⟩ := win
  obtain ⟨i,j,_,_,_,_,shape,_,_,_,_⟩ := strict_eight_true_factor_peak F paid eight
  have pair : F.n i+F.m j=10 := by omega
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤8 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq eight
  have highest : widthAt F.n F.m F.r 9=highestWidth F.n F.m F.r := by
    rw [show 9=diagonal F.n F.m (F.r+2) by omega,width_at_peak F.hs F.ht F.n F.m F.hn F.hm]
  by_cases even:Even a
  · have odd : Odd b := by rw [Nat.even_iff] at even;rw [Nat.odd_iff];omega
    have price := near_top_dead_count_price F.G F.n F.m F.hn F.hm even odd height ap red blue
      ⟨i,j,pair⟩ cap F.row M small small'
    rwa [←eq,highest] at price
  · have odd := Nat.not_even_iff_odd.mp even
    have eb : Even b := by rw [Nat.odd_iff] at odd;rw [Nat.even_iff];omega
    have price := near_top_dead_count_price F.G F.m F.n F.hm F.hn eb odd (by omega : b+a-1=8) bp blue red
      ⟨j,i,by omega⟩ cap (swap_positive_forcing_row F.G _ _ F.row) M small' small
    rwa [Nat.add_comm (originalThresholdCount F.m b),←eq,width_at_swap F.m F.n,highest] at price

theorem eighth_column_after_fixed_cut (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (H:EightSevenSixHistory (F.G.induce (componentVertices F.G T)ᶜ)) (a b z:ℕ) (ra:3≤a) (bl:3≤b)
    (za:z≤a) (zb:z≤b) (win:WinsHeight F.n F.m F.r 8 a b) :
    let O := F.G.induce (componentVertices F.G T)ᶜ
    let Y := O.induce H.eightᶜ
    let L := widthAt F.n F.m F.r 8
    let M := chosenSlots F.G T z
    let h := highestWidth F.n F.m F.r
    (L-H.eight.ncard≤M+(h-1)) ∨
      ∃k≤M,(L-k-H.eight.ncard)+2≤minimumExposure Y 7 ∧
        ((a=6 ∨ b=6) → (L-k-H.eight.ncard)+4≤minimumExposure Y 7) ∧ 0<L-k-H.eight.ncard := by
  intro O Y L M h
  rcases actual_mono_width_or_two_small_counts F.G T F.n F.m F.hn F.hm za zb win F.row with ⟨k,cost,typed⟩|⟨left,right⟩
  · by_cases gone:L-k-H.eight.ncard=0
    · left;omega
    have capO (v) : Nat.card (O.neighborSet v)≤8 := (induced_neighbor_count_le F.G _ v).trans
      (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq eight)
    have cap := (H.caps capO).1
    have now := typed_width_after_deletion O H.eight win.1 win.2.1 typed
    have charge := seven_typed_signed_charge Y cap a b (L-k-H.eight.ncard) ra bl win.2.2.1 now
    obtain ⟨pay,high⟩ := charge.resolve_left gone
    exact Or.inr ⟨k,cost,pay,high,by omega⟩
  · have aSmall := left.trans (chosen_slots_antitone F.G T za)
    have bSmall := right.trans (chosen_slots_antitone F.G T zb)
    have dead := oriented_eight_dead_price F paid eight a b M win aSmall bSmall
    change L≤M+(h-1) at dead
    left;omega

#print axioms oriented_eight_dead_price
#print axioms eighth_column_after_fixed_cut
end JSP452Audit.StarHost
