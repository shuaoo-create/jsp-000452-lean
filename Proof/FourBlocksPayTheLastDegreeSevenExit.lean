import LowDegreeRegularExitsWithTheirProvenVolume
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem width_six_seven_scalar (P eps h s q b c g L8 L9 L10 M2 M3 M4 M5:ℕ)
    (large:21≤P) (width:h=6) (pair:eps=2) (short:s+5≤P) (two:3*M2≤2*P+eps) (three:4*M3≤2*P+eps)
    (four:5*M4≤2*P+eps) (five:6*M5≤2*P+eps) (top:L10≤c+M4+(h-1)) (middle:L9≤g+M3+M5)
    (platform:L8≤P ∨ L8≤s+M2+q+4) (charge:q+3*P+5*eps+1+(b+c+g)≤L8+L9+L10+h) : False := by
  subst eps;subst h
  have volume : M2+M3+M4+M5≤2*P := by omega
  rcases platform with _|_ <;> omega
theorem width_six_seven_exit_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F) (six:highestWidth F.n F.m F.r=6) (pair:A.K.eps=2) (large:21≤A.K.P) (slack:1≤A.K.slack)
    (short:A.steps+5≤A.K.P) (H:TenLowHistory (F.G.induce A.K.supportᶜ))
    (E:TenRegularExit A 7 (H.high.upper.ncard+H.high.midCut.ncard+H.high.lastCut.ncard)) : False := by
  let O := F.G.induce A.K.supportᶜ
  let h := highestWidth F.n F.m F.r
  let L := widthAt F.n F.m F.r
  let M := chosenSlots F.G A.K.selected
  have hp := (strict_ten_inventory F paid ten).1
  have ep := A.K.positive
  have volume := width_six_conservative_capacity F paid ten A six pair slack
  obtain ⟨red,blue⟩ := width_six_regular_heads_at_most_seven F paid ten A six pair large slack
  have cap (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have lo8 := (H.high.degree_caps cap).2.1
  have lo7 := (H.remaining_caps cap).1
  have top := ten_tenth_column_on_first_cut F paid ten A.K H.high.midCut
    (fun v => (lo8 v).trans (by decide : 8≤9)) 4 (by decide) (fun i => by have := red i;omega) (fun i => by have := blue i;omega)
  have zero9 := zero_exposure_above_every_degree (O.induce H.high.midCutᶜ) 9 (fun v => Nat.lt_succ_of_le (lo8 v))
  change L 10-H.high.midCut.ncard≤M 4+max (h-1) (minimumExposure (O.induce H.high.midCutᶜ) 9-2) at top
  rw [zero9] at top
  have mid := ten_regular_platform_on_its_graph F A.K 9 3 5 (by decide) (by decide) (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega) H.high.lastCut (fun v => (lo7 v).trans (by decide : 7≤8))
  change (L 9≤A.K.P ∧ L 9≤M 3+M 5) ∨ L 9≤H.high.lastCut.ncard+M 3+minimumExposure (O.induce H.high.lastCutᶜ) 8 at mid
  rw [zero_exposure_above_every_degree _ 8 (fun v => Nat.lt_succ_of_le (lo7 v))] at mid
  have base := ten_regular_platform_on_its_graph F A.K 8 2 4 (by decide) (by decide) (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega) E.vertexSet E.cap
  change (L 8≤A.K.P ∧ _) ∨ L 8≤E.vertexSet.ncard+M 2+minimumExposure E.graph 7 at base
  rw [E.length] at base
  have exp := E.seven_exposure_from_volume paid ten volume
  have fee := (E.row_price_from_volume paid ten volume (by decide)).2.2.2.2.2
  have orig : L 11=h := by change widthAt F.n F.m F.r 11=_;rw [show 11=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm]
  change E.surplus+3*A.K.P+5*A.K.eps+1+_≤∑j∈Finset.range 4,L (7+j+1) at fee
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.zero_add] at fee
  change _≤L 8+L 9+L 10+L 11 at fee
  rw [orig] at fee
  exact width_six_seven_scalar A.K.P A.K.eps h A.steps E.surplus H.high.upper.ncard H.high.midCut.ncard H.high.lastCut.ncard
    (L 8) (L 9) (L 10) (M 2) (M 3) (M 4) (M 5) large six pair short
    (ten_regular_slot_volume A.K 2) (ten_regular_slot_volume A.K 3) (ten_regular_slot_volume A.K 4) (ten_regular_slot_volume A.K 5)
    (by omega) (by omega) (by omega) fee

#print axioms width_six_seven_scalar
#print axioms width_six_seven_exit_impossible
end JSP452Audit.StarHost
