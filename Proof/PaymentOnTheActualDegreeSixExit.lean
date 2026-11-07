import PaymentOnTheActualDegreeSevenExit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_exit_scalar_incompatible (P eps h s q b c g l L7 L8 L9 L10 M2 M5:ℕ)
    (mass:5≤P) (ep:1≤eps) (sm:eps≤2) (cases:h=1 ∨ (eps=2 ∧ (h≤2 ∨ (10≤P ∧ h≤5))))
    (step:s<P) (short:h≤2 ∨ s+5≤P) (two:3*M2≤2*P+eps) (five:6*M5≤2*P+eps)
    (top:L10≤c+M5+(h-1)) (near:L9≤g+P) (middle:L8≤l+P)
    (platform:L7≤P ∨ L7≤s+M2+q+4)
    (charge:q+4*P+5*eps+1+(b+c+g+l)≤L7+L8+L9+L10+h) : False := by
  have slots : 2*(M2+M5)≤2*P+eps := by omega
  rcases cases with one|⟨e,low|⟨_,hi⟩⟩ <;> rcases platform with v|v <;> omega

theorem ten_regular_six_exit_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F) (cases:TenRegularCases F A)
    (short:highestWidth F.n F.m F.r≤2 ∨ A.steps+5≤A.K.P) (red:∀i,F.n i≤6) (blue:∀i,F.m i≤6)
    (H:TenLowHistory (F.G.induce A.K.supportᶜ))
    (E:TenRegularExit A 6 (H.high.upper.ncard+H.high.midCut.ncard+H.high.lastCut.ncard+H.sevenCut.ncard)) : False := by
  let O := F.G.induce A.K.supportᶜ
  let h := highestWidth F.n F.m F.r
  let L := widthAt F.n F.m F.r
  let M := chosenSlots F.G A.K.selected
  have ep := A.K.positive
  have cost : 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 := by unfold TenRegularCases at cases;omega
  have cap (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have lo8 := (H.high.degree_caps cap).2.1
  obtain ⟨lo7,lo6,_⟩ := H.remaining_caps cap
  have top := ten_tenth_column_on_first_cut F paid ten A.K H.high.midCut
    (fun v => (lo8 v).trans (by decide : 8≤9)) 5 (by decide) (fun i => by have := red i;omega) (fun i => by have := blue i;omega)
  change L 10-H.high.midCut.ncard≤M 5+max (h-1) (minimumExposure (O.induce H.high.midCutᶜ) 9-2) at top
  rw [zero_exposure_above_every_degree _ 9 (fun v => Nat.lt_succ_of_le (lo8 v))] at top
  have room := ten_regular_slot_volume A.K 2
  change 3*M 2≤2*A.K.P+A.K.eps at room
  have min := A.K.minimum_order
  have sm := A.K.small
  have near := ten_regular_platform_on_its_graph F A.K 9 2 4 (by decide) (by decide) (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega) H.high.lastCut (fun v => (lo7 v).trans (by decide : 7≤8))
  change (L 9≤A.K.P ∧ _) ∨ L 9≤H.high.lastCut.ncard+M 2+minimumExposure (O.induce H.high.lastCutᶜ) 8 at near
  rw [zero_exposure_above_every_degree _ 8 (fun v => Nat.lt_succ_of_le (lo7 v))] at near
  have mid := ten_regular_platform_on_its_graph F A.K 8 2 4 (by decide) (by decide) (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega) H.sevenCut (fun v => (lo6 v).trans (by decide : 6≤7))
  change (L 8≤A.K.P ∧ _) ∨ L 8≤H.sevenCut.ncard+M 2+minimumExposure (O.induce H.sevenCutᶜ) 7 at mid
  rw [zero_exposure_above_every_degree _ 7 (fun v => Nat.lt_succ_of_le (lo6 v))] at mid
  have base := ten_regular_platform_on_its_graph F A.K 7 2 4 (by decide) (by decide) (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega) E.vertexSet E.cap
  change (L 7≤A.K.P ∧ _) ∨ L 7≤E.vertexSet.ncard+M 2+minimumExposure E.graph 6 at base
  rw [E.length] at base
  have exp := E.six_exposure paid ten cases
  have fee := (E.exact_row_price paid ten cases (by decide)).2.2.2.2.2
  have orig : L 11=h := by change widthAt F.n F.m F.r 11=_;rw [show 11=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm]
  change E.surplus+4*A.K.P+5*A.K.eps+1+_≤∑j∈Finset.range 5,L (6+j+1) at fee
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.zero_add] at fee
  change _≤L 7+L 8+L 9+L 10+L 11 at fee
  rw [orig] at fee
  exact six_exit_scalar_incompatible A.K.P A.K.eps h A.steps E.surplus H.high.upper.ncard H.high.midCut.ncard H.high.lastCut.ncard
    H.sevenCut.ncard (L 7) (L 8) (L 9) (L 10) (M 2) (M 5) min ep sm cases (A.step_bounds paid ten cost).2.1 short
    room (ten_regular_slot_volume A.K 5) (by omega) (by omega) (by omega) (by omega) fee

theorem strict_ten_regular_source_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F) (cases:TenRegularCases F A)
    (short:highestWidth F.n F.m F.r≤2 ∨ A.steps+5≤A.K.P) : False := by
  obtain ⟨H⟩ := ten_low_history_exists (F.G.induce A.K.supportᶜ)
  rcases ten_regular_lower_exit_exists F paid ten A cases H with seven|⟨red,blue,six⟩
  · exact ten_regular_seven_exit_impossible F paid ten A cases short H (Classical.choice seven)
  · exact ten_regular_six_exit_impossible F paid ten A cases short red blue H (Classical.choice six)

#print axioms six_exit_scalar_incompatible
#print axioms ten_regular_six_exit_impossible
#print axioms strict_ten_regular_source_impossible
end JSP452Audit.StarHost
