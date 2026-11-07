import EightMissingNeighborsPerRegularComponent
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem seven_typed_signed_charge {X:Type*} [Finite X] (G:SimpleGraph X) (cap:∀v,Nat.card (G.neighborSet v)≤7)
    (a b l:ℕ) (ha:3≤a) (hb:3≤b) (height:a+b-1=8) (typed:ExactTypedWidth G a b l) :
    l=0 ∨ (l+2≤minimumExposure G 7 ∧ ((a=6 ∨ b=6) → l+4≤minimumExposure G 7)) := by
  rcases typed with zero|⟨u,v,hu,hv,wide,force⟩
  · exact Or.inl zero
  · right
    have shapes : (a=3 ∧ b=6) ∨ (a=4 ∧ b=5) ∨ (a=5 ∧ b=4) ∨ (a=6 ∧ b=3) := by omega
    rcases shapes with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · have need := seven_signed_three_six G cap v u hv hu (forces_swap force);dsimp only at need;omega
    · have need := seven_signed_four_five G cap u v hu hv force;dsimp only at need;omega
    · have need := seven_signed_four_five G cap v u hv hu (forces_swap force);dsimp only at need;omega
    · have need := seven_signed_three_six G cap u v hu hv force;dsimp only at need;omega

theorem strict_eighth_typed_winner (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) :
    ∃a b:ℕ,3≤a ∧ 3≤b ∧ WinsHeight F.n F.m F.r 8 a b ∧ ExactTypedWidth F.G a b (widthAt F.n F.m F.r 8) := by
  have live : 0<widthAt F.n F.m F.r 8 := (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by omega⟩
  obtain ⟨a,b,ap,bp,height,rf,bg,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by decide : 0<8) live
  obtain ⟨reds,blues⟩ := strict_eight_no_seven_head F paid eight
  have x := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).2 rf
  have y := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).2 bg
  have na := reds ⟨0,F.hs⟩
  have mb := blues ⟨0,F.ht⟩
  have typed := typed_width_of_original_rectangle F.G F.n F.m F.hn F.hm rf bg F.row
  exact ⟨a,b,by omega,by omega,⟨ap,bp,height,rf,bg,win⟩,win ▸ typed⟩

theorem strict_eight_signed_first_residual (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (S:Set F.X) (stage:CompleteDegreeStage F.G 8 S) :
    let Y := F.G.induce Sᶜ
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 8
    minimumExposure Y 7≤(22+2*h)/5 ∧ L-S.ncard≤(22+2*h)/5-2 := by
  intro Y h L
  obtain ⟨a,b,lowA,lowB,win,typed⟩ := strict_eighth_typed_winner F paid eight
  obtain ⟨ap,bp,height,_,_,_⟩ := win
  have remain := typed_width_after_deletion F.G S ap bp typed
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have low (x) : Nat.card (Y.neighborSet x)≤7 := by
    have v := complete_stage_lowers_cap F.G 8 S (fun x => (cap x).trans_eq eight) stage x
    change Nat.card (Y.neighborSet x)<8 at v;omega
  have signed := seven_typed_signed_charge Y low a b (L-S.ncard) lowA lowB height remain
  have fee := (strict_eight_complete_stage F paid eight S stage).2.2.2.2.2
  change 5*minimumExposure Y 7≤22+2*h at fee
  rcases signed with zero|⟨charge,_⟩ <;> omega

#print axioms seven_typed_signed_charge
#print axioms strict_eighth_typed_winner
#print axioms strict_eight_signed_first_residual
end JSP452Audit.StarHost
