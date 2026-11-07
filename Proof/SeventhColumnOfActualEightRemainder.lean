import ActualMonochromeColumnOutcomes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem seven_pair_slot_sum {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    (x y:ℕ) (red:2≤x) (blue:2≤y) (height:x+y-1=7) :
    chosenSlots G T x+chosenSlots G T y≤∑c∈T,Nat.card c.supp/2 := by
  have per (c:G.ConnectedComponent) : Nat.card c.supp/(x+1)+Nat.card c.supp/(y+1)≤Nat.card c.supp/2 := by
    have cases : (x=2 ∧ y=6) ∨ (x=3 ∧ y=5) ∨ (x=4 ∧ y=4) ∨ (x=5 ∧ y=3) ∨ (x=6 ∧ y=2) := by omega
    rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  have sum := Finset.sum_le_sum (s:=T) (fun c _ => per c)
  rwa [Finset.sum_add_distrib] at sum

theorem seven_column_survives_or_within_half_order (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (H:EightSevenSixHistory (F.G.induce (componentVertices F.G T)ᶜ)) :
    let O := F.G.induce (componentVertices F.G T)ᶜ
    let Y := O.induce H.sevenCutᶜ
    let L := widthAt F.n F.m F.r 7
    L≤(∑c∈T,Nat.card c.supp/2) ∨ L-H.sevenCut.ncard≤chosenSlots F.G T 2+minimumExposure Y 6 := by
  intro O Y L
  by_cases live:0<L
  · obtain ⟨a,b,ap,bp,height,rf,bg,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by decide : 0<7) live
    have aHead := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 rf
    have bHead := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 bg
    obtain ⟨red,blue⟩ := strict_eight_no_seven_head F paid eight
    have topR := red ⟨0,F.hs⟩
    have topB := blue ⟨0,F.ht⟩
    have x : 2≤a := by omega
    have y : 2≤b := by omega
    rcases actual_mono_width_or_two_small_counts F.G T F.n F.m F.hn F.hm x y ⟨ap,bp,height,rf,bg,win⟩ F.row with ⟨k,cost,typed⟩|⟨small,small'⟩
    · right
      have capO (v) : Nat.card (O.neighborSet v)≤8 := (induced_neighbor_count_le F.G _ v).trans
        (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq eight)
      have cap := (H.caps capO).2.1
      have current := typed_width_after_deletion O H.sevenCut ap bp typed
      have exposed := typed_width_exposure_at_cap Y 6 a b (L-k-H.sevenCut.ncard) (by decide) cap ap bp height current
      omega
    · have slots := seven_pair_slot_sum F.G T a b x y height
      change L=_ at win;left;omega
  · left;omega

#print axioms seven_pair_slot_sum
#print axioms seven_column_survives_or_within_half_order
end JSP452Audit.StarHost
