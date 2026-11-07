import ACommonOrderBudgetForActualTenRegularComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem strict_tenth_column_slot_tax (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (T:Finset F.G.ConnectedComponent) (z:ℕ)
    (redMax:∀i,F.n i+z≤11) (blueMax:∀j,F.m j+z≤11) :
    let O := F.G.induce (componentVertices F.G T)ᶜ
    widthAt F.n F.m F.r 10≤uniformEnvelope O 10+chosenSlots F.G T z+(highestWidth F.n F.m F.r-1) := by
  intro O
  by_cases live:0<widthAt F.n F.m F.r 10
  · obtain ⟨a,b,ha,hb,height,red,blue,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by decide : 0<10) live
    have headA := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
    have headB := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
    have maxA := redMax ⟨0,F.hs⟩
    have maxB := blueMax ⟨0,F.ht⟩
    have lowA : z≤a := by omega
    have lowB : z≤b := by omega
    have monA := chosen_slots_antitone F.G T lowA
    have monB := chosen_slots_antitone F.G T lowB
    have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤10 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
    obtain ⟨i,j,_,_,_,_,shape,_,_,_,_⟩ := strict_ten_true_factor_peak F paid ten
    have peak : F.n i+F.m j=12 := by omega
    have orig : widthAt F.n F.m F.r 11=highestWidth F.n F.m F.r := by
      rw [show 11=diagonal F.n F.m (F.r+2) by omega,width_at_peak F.hs F.ht F.n F.m F.hn F.hm]
    have positive := (strict_ten_inventory F paid ten).1
    have pw : 0<widthAt F.n F.m F.r 11 := by omega
    by_cases ea:Even a
    · have ob : Odd b := by rw [Nat.even_iff] at ea;rw [Nat.odd_iff];omega
      have fee := near_top_even_direction F.G T F.n F.m F.hn F.hm ea ob ha hb height red blue pw ⟨i,j,peak⟩ cap F.row
      rw [←win,orig] at fee;change _≤uniformEnvelope O 10+_ at fee;omega
    · have oa := Nat.not_even_iff_odd.mp ea
      have eb : Even b := by rw [Nat.odd_iff] at oa;rw [Nat.even_iff];omega
      have swap := width_at_swap F.m F.n F.r 11
      have fee := near_top_even_direction F.G T F.m F.n F.hm F.hn eb oa hb ha (by omega : b+a-1=10) blue red
        (by rwa [swap]) ⟨j,i,by omega⟩ cap (swap_positive_forcing_row F.G _ _ F.row)
      rw [Nat.add_comm (originalThresholdCount F.m b),←win,swap,orig] at fee
      change _≤uniformEnvelope O 10+_ at fee;omega
  · omega


theorem ten_closed_low_column_tax (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) (j:ℕ) (pos:0<j) :
    widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce K.supportᶜ) j+K.P := by
  have lengths := (strict_closed_union_lengths F paid K.support K.support_closed (fun x hx => (K.support_full x hx).trans ten.symm)).1
  have size : K.support.ncard=2*K.P+K.eps := K.order
  have small := K.small
  exact closed_union_column_tax F.G K.support K.support_closed F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm pos
    K.fits (by omega) (by omega) F.row
#print axioms strict_tenth_column_slot_tax
#print axioms ten_closed_low_column_tax
end JSP452Audit.StarHost
