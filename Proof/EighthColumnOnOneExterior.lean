import FixedExteriorNearTopDirection
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem width_at_swap {s t:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (r j:ℕ) : widthAt n m r j=widthAt m n r j := by
  have eq : offsetsAt n m r j=offsetsAt m n r j := by
    ext i
    simp only [offsetsAt,Finset.mem_filter,Finset.mem_range]
    rw [show rowCount s t r=rowCount t s r by simp [rowCount,Nat.add_comm],diagonal_swap n m]
  exact congrArg Finset.card eq

theorem chosen_slots_antitone {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent) :
    Antitone (chosenSlots G T) := by
  intro a b le;apply Finset.sum_le_sum;intro c _
  exact Nat.div_le_div_left (by omega : a+1≤b+1) (by omega : 0<a+1)

theorem strict_eighth_column_slot_tax (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (z:ℕ)
    (redMax:∀i,F.n i+z≤9) (blueMax:∀j,F.m j+z≤9) :
    let O := F.G.induce (componentVertices F.G T)ᶜ
    widthAt F.n F.m F.r 8≤uniformEnvelope O 8+chosenSlots F.G T z+(highestWidth F.n F.m F.r-1) := by
  intro O
  by_cases live:0<widthAt F.n F.m F.r 8
  · obtain ⟨a,b,ha,hb,height,red,blue,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by decide : 0<8) live
    have headA := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
    have headB := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
    have maxA := redMax ⟨0,F.hs⟩
    have maxB := blueMax ⟨0,F.ht⟩
    have lowA : z≤a := by omega
    have lowB : z≤b := by omega
    have monA := chosen_slots_antitone F.G T lowA
    have monB := chosen_slots_antitone F.G T lowB
    have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤8 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq eight
    obtain ⟨i,j,_,_,_,_,shape,_,_,_,_⟩ := strict_eight_true_factor_peak F paid eight
    have peak : F.n i+F.m j=10 := by omega
    have orig : widthAt F.n F.m F.r 9=highestWidth F.n F.m F.r := by
      rw [show 9=diagonal F.n F.m (F.r+2) by omega,width_at_peak F.hs F.ht F.n F.m F.hn F.hm]
    have positive := (strict_eight_inventory F paid eight).1
    have pw : 0<widthAt F.n F.m F.r 9 := by omega
    by_cases ea:Even a
    · have ob : Odd b := by rw [Nat.even_iff] at ea;rw [Nat.odd_iff];omega
      have fee := near_top_even_direction F.G T F.n F.m F.hn F.hm ea ob ha hb height red blue pw ⟨i,j,peak⟩ cap F.row
      rw [←win,orig] at fee;change _≤uniformEnvelope O 8+_ at fee;omega
    · have oa := Nat.not_even_iff_odd.mp ea
      have eb : Even b := by rw [Nat.odd_iff] at oa;rw [Nat.even_iff];omega
      have swap := width_at_swap F.m F.n F.r 9
      have fee := near_top_even_direction F.G T F.m F.n F.hm F.hn eb oa hb ha (by omega : b+a-1=8) blue red
        (by rwa [swap]) ⟨j,i,by omega⟩ cap (swap_positive_forcing_row F.G _ _ F.row)
      rw [Nat.add_comm (originalThresholdCount F.m b),←win,swap,orig] at fee
      change _≤uniformEnvelope O 8+_ at fee;omega
  · omega

#print axioms width_at_swap
#print axioms chosen_slots_antitone
#print axioms strict_eighth_column_slot_tax
end JSP452Audit.StarHost
