import OrientedEighthColumnRecovery
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eighth_column_small_remaining_bounds (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (types:EightSelectionSize T.card (highestWidth F.n F.m F.r))
    (H:EightSevenSixHistory (F.G.induce (componentVertices F.G T)ᶜ)) :
    let L := widthAt F.n F.m F.r 8
    let b := H.eight.ncard
    (T.card=1 → L-b≤max (chosenSlots F.G T 3) (chosenSlots F.G T 4+2)) ∧
      (2≤T.card → L-b≤chosenSlots F.G T 3+4) := by
  intro L b
  let h := highestWidth F.n F.m F.r
  let O := F.G.induce (componentVertices F.G T)ᶜ
  let rho := minimumExposure (O.induce H.eightᶜ) 7
  have lower := (strict_signed_first_stage_on_exterior F paid eight T actual H).2
  change rho≤(22+2*h)/5 at lower
  have maxH : h≤5 := by change EightSelectionSize T.card h at types;unfold EightSelectionSize at types;omega
  obtain ⟨x,y,red,blue,win,_⟩ := strict_eighth_typed_winner F paid eight
  have hi := win.2.2.1
  have long := eighth_column_after_fixed_cut F paid eight T H x y 3 red blue red blue win
  change L-b≤chosenSlots F.G T 3+(h-1) ∨ ∃k≤chosenSlots F.G T 3,
    L-k-b+2≤rho ∧ ((x=6 ∨ y=6) → L-k-b+4≤rho) ∧ 0<L-k-b at long
  constructor
  · intro one
    have oneH : h=1 := by change EightSelectionSize T.card h at types;unfold EightSelectionSize at types;omega
    by_cases isSix:x=6 ∨ y=6
    · rcases long with dead|⟨k,price,_,charge,pos⟩
      · omega
      · have := charge isSix;omega
    · have gx : 4≤x := by clear * - red blue hi isSix;omega
      have gy : 4≤y := by clear * - red blue hi isSix;omega
      have near := eighth_column_after_fixed_cut F paid eight T H x y 4 red blue gx gy win
      change L-b≤chosenSlots F.G T 4+(h-1) ∨ ∃k≤chosenSlots F.G T 4,
        L-k-b+2≤rho ∧ ((x=6 ∨ y=6) → L-k-b+4≤rho) ∧ 0<L-k-b at near
      rcases near with dead|⟨k,price,charge,_,pos⟩ <;> omega
  · intro _
    rcases long with dead|⟨k,price,charge,_,pos⟩ <;> omega

theorem chosen_width_four_slot_bound {X:Type*} [Finite X] (G:SimpleGraph X) (T:Finset G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents G 8) :
    5*chosenSlots G T 4≤2*(∑c∈T,Nat.card c.supp/2)+T.card := by
  have each (c) (hc:c∈T) : 5*(Nat.card c.supp/5)≤2*(Nat.card c.supp/2)+1 := by
    obtain ⟨n,eq⟩ := (actual c hc).1;omega
  have sum := Finset.sum_le_sum (s:=T) each
  rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const] at sum
  simpa only [chosenSlots,nsmul_eq_mul,Nat.cast_id,mul_one] using sum

#print axioms eighth_column_small_remaining_bounds
#print axioms chosen_width_four_slot_bound
end JSP452Audit.StarHost
