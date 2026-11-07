import PricesAcrossTheSameTenAndNineDegreeHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_signed_first_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (reds:∀i,F.n i≤8) (blues:∀j,F.m j≤8)
    (S:Set F.X) (stage:CompleteDegreeStage F.G 10 S) :
    widthAt F.n F.m F.r 10-S.ncard≤(38+2*highestWidth F.n F.m F.r)/7-2 := by
  let Y := F.G.induce Sᶜ
  let L := widthAt F.n F.m F.r 10
  have live : 0<L := (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by omega⟩
  obtain ⟨a,b,ap,bp,h,red,blue,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<10) live
  have ar := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 red
  have br := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 blue
  have nMax := reds ⟨0,F.hs⟩
  have mMax := blues ⟨0,F.ht⟩
  have typed := typed_width_of_original_rectangle F.G F.n F.m F.hn F.hm red blue F.row
  have starting : ExactTypedWidth F.G a b L := by change ExactTypedWidth F.G a b (widthAt F.n F.m F.r 10);rw [win];exact typed
  have remain := typed_width_after_deletion F.G S ap bp starting
  have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  have low (x) : Nat.card (Y.neighborSet x)≤9 := Nat.le_of_lt_succ (complete_stage_lowers_cap F.G 10 S cap stage x)
  have fee := (strict_ten_complete_stage F paid ten S stage).2.2.2.2.2
  change 7*minimumExposure Y 9≤38+2*highestWidth F.n F.m F.r at fee
  change L-S.ncard≤_
  rcases remain with zero|⟨u,v,hu,hv,wide,force⟩
  · omega
  · have signed := (nine_uniform_signed_alternatives Y low a b u v (by omega) (by omega) (by omega) hu hv force).1
    change u+v-1+2≤minimumExposure Y 9 at signed
    omega

theorem ten_short_head_regular_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (reds:∀i,F.n i≤8) (blues:∀j,F.m j≤8)
    (K:TenRegularBudget F.G) (I:Set ↥K.support) (inner:CompleteDegreeStage (F.G.induce K.support) 10 I)
    (B:Set ↥(K.supportᶜ:Set F.X)) (first:CompleteDegreeStage (F.G.induce K.supportᶜ) 10 B) :
    widthAt F.n F.m F.r 10≤I.ncard+B.ncard+((38+2*highestWidth F.n F.m F.r)/7-2) := by
  obtain ⟨both,size⟩ := join_closed_degree_stages F.G K.support 10 K.support_closed I B inner first
  have signed := ten_signed_first_stage F paid ten reds blues _ both
  omega

#print axioms ten_signed_first_stage
#print axioms ten_short_head_regular_stage
end JSP452Audit.StarHost
