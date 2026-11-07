import BothExposuresOnOneTenDegreeExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem oriented_ten_dead_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (a b M:ℕ) (win:WinsHeight F.n F.m F.r 10 a b)
    (small:originalThresholdCount F.n a≤M) (small':originalThresholdCount F.m b≤M) :
    widthAt F.n F.m F.r 10≤M+(highestWidth F.n F.m F.r-1) := by
  obtain ⟨ap,bp,height,red,blue,eq⟩ := win
  obtain ⟨i,j,_,_,_,_,shape,_,_,_,_⟩ := strict_ten_true_factor_peak F paid ten
  have pair : F.n i+F.m j=12 := by omega
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤10 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  have highest : widthAt F.n F.m F.r 11=highestWidth F.n F.m F.r := by
    rw [show 11=diagonal F.n F.m (F.r+2) by omega,width_at_peak F.hs F.ht F.n F.m F.hn F.hm]
  by_cases even:Even a
  · have odd : Odd b := by rw [Nat.even_iff] at even;rw [Nat.odd_iff];omega
    have price := near_top_dead_count_price F.G F.n F.m F.hn F.hm even odd height ap red blue
      ⟨i,j,pair⟩ cap F.row M small small'
    rwa [←eq,highest] at price
  · have odd := Nat.not_even_iff_odd.mp even
    have eb : Even b := by rw [Nat.odd_iff] at odd;rw [Nat.even_iff];omega
    have price := near_top_dead_count_price F.G F.m F.n F.hm F.hn eb odd (by omega : b+a-1=10) bp blue red
      ⟨j,i,by omega⟩ cap (swap_positive_forcing_row F.G _ _ F.row) M small' small
    rwa [Nat.add_comm (originalThresholdCount F.m b),←eq,width_at_swap F.m F.n,highest] at price



theorem ten_tenth_column_on_first_cut (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) (V:Set ↥(K.supportᶜ:Set F.X))
    (low:∀v,Nat.card (((F.G.induce K.supportᶜ).induce Vᶜ).neighborSet v)≤9)
    (z:ℕ) (minHead:3≤z) (redMax:∀i,F.n i+z≤11) (blueMax:∀j,F.m j+z≤11) :
    let L := widthAt F.n F.m F.r 10
    let M := chosenSlots F.G K.selected z
    let h := highestWidth F.n F.m F.r
    let rho := minimumExposure ((F.G.induce K.supportᶜ).induce Vᶜ) 9
    L-V.ncard≤M+max (h-1) (rho-2) := by
  intro L M h rho
  have live : 0<L := (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by omega⟩
  obtain ⟨a,b,ap,bp,ht,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<10) live
  have orig : WinsHeight F.n F.m F.r 10 a b := ⟨ap,bp,ht,red,blue,w⟩
  have ar := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
  have br := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
  have nMax := redMax ⟨0,F.hs⟩
  have mMax := blueMax ⟨0,F.ht⟩
  have ax : z≤a := by omega
  have bx : z≤b := by omega
  rcases actual_mono_width_or_two_small_counts F.G K.selected F.n F.m F.hn F.hm ax bx orig F.row with ⟨k,price,typed⟩|⟨small,small'⟩
  · have current := typed_width_after_deletion (F.G.induce K.supportᶜ) V ap bp typed
    change ExactTypedWidth ((F.G.induce K.supportᶜ).induce Vᶜ) a b (L-k-V.ncard) at current
    change k≤M at price
    rcases current with eq|⟨u,v,pu,pv,wide,force⟩
    · omega
    · have signed := (nine_uniform_signed_alternatives _ low a b u v (by omega) (by omega) (by omega) pu pv force).1
      change u+v-1+2≤rho at signed
      omega
  · have dead := oriented_ten_dead_price F paid ten a b M orig
      (small.trans (chosen_slots_antitone F.G K.selected ax)) (small'.trans (chosen_slots_antitone F.G K.selected bx))
    change L≤M+(h-1) at dead
    omega

#print axioms oriented_ten_dead_price
#print axioms ten_tenth_column_on_first_cut
end JSP452Audit.StarHost
