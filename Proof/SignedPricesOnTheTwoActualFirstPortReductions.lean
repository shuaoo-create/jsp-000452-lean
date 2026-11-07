import KeepBothOriginalHeadTypesForTheFinalPortPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_signed_port_tenth_column (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G} {w:ℕ} (W:TenPortSupport F.G K w) (V:Set ↥(W.supportᶜ:Set F.X))
    (low:∀v,Nat.card ((W.outside.induce Vᶜ).neighborSet v)≤9)
    (z:ℕ) (minHead:3≤z) (redMax:∀i,F.n i+z≤11) (blueMax:∀j,F.m j+z≤11) :
    let L := widthAt F.n F.m F.r 10
    let M := W.slotDamage z
    let h := highestWidth F.n F.m F.r
    let rho := minimumExposure (W.outside.induce Vᶜ) 9
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
  rcases W.retained_type_or_two_small_heads F.n F.m F.hn F.hm ax bx orig F.row with ⟨k,price,typed⟩|⟨small,small'⟩
  · have current := typed_width_after_deletion W.outside V ap bp typed
    change ExactTypedWidth (W.outside.induce Vᶜ) a b (L-k-V.ncard) at current
    change k≤M at price
    rcases current with eq|⟨u,v,pu,pv,wide,force⟩
    · omega
    · have signed := (nine_uniform_signed_alternatives _ low a b u v (by omega) (by omega) (by omega) pu pv force).1
      change u+v-1+2≤rho at signed
      omega
  · have dead := oriented_ten_dead_price F paid ten a b M orig
      (small.trans (W.port_slot_decreases ax)) (small'.trans (W.port_slot_decreases bx))
    change L≤M+(h-1) at dead
    omega

theorem ten_signed_port_original_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (reds:∀i,F.n i≤8) (blues:∀j,F.m j≤8)
    (S:Set F.X) (low:∀v,Nat.card ((F.G.induce Sᶜ).neighborSet v)≤9) :
    widthAt F.n F.m F.r 10-S.ncard≤minimumExposure (F.G.induce Sᶜ) 9-2 := by
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
  change L-S.ncard≤minimumExposure Y 9-2
  rcases remain with zero|⟨u,v,hu,hv,wide,force⟩
  · omega
  · have signed := (nine_uniform_signed_alternatives Y low a b u v (by omega) (by omega) (by omega) hu hv force).1
    change u+v-1+2≤minimumExposure Y 9 at signed
    omega

#print axioms ten_signed_port_tenth_column
#print axioms ten_signed_port_original_stage
end JSP452Audit.StarHost
