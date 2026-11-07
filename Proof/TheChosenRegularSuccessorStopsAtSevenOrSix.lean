import FiveActualStagesOnTheSameExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def TenRegularCases (F:StrictFamily.{u}) (A:PricedTenMenu F) : Prop :=
  highestWidth F.n F.m F.r=1 ∨ (A.K.eps=2 ∧ (highestWidth F.n F.m F.r≤2 ∨
      (10≤A.K.P ∧ highestWidth F.n F.m F.r≤5)))

structure TenRegularExit {F:StrictFamily.{u}} (A:PricedTenMenu F) (a income:ℕ) where
  vertexSet : Set ↥(A.K.supportᶜ:Set F.X)
  length : vertexSet.ncard=A.steps
  cap : ∀x,Nat.card (((F.G.induce A.K.supportᶜ).induce vertexSetᶜ).neighborSet x)≤a
  price : (F.G.induce A.K.supportᶜ).edgeSet.ncard=((F.G.induce A.K.supportᶜ).induce vertexSetᶜ).edgeSet.ncard+a*A.steps+income

theorem ten_regular_lower_exit_exists (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F) (cases:TenRegularCases F A)
    (H:TenLowHistory (F.G.induce A.K.supportᶜ)) :
    let b := H.high.upper.ncard
    let c := H.high.midCut.ncard
    let g := H.high.lastCut.ncard
    let l := H.sevenCut.ncard
    Nonempty (TenRegularExit A 7 (b+c+g)) ∨
      ((∀i,F.n i≤6) ∧ (∀i,F.m i≤6) ∧ Nonempty (TenRegularExit A 6 (b+c+g+l))) := by
  intro b c g l
  let O := F.G.induce A.K.supportᶜ
  have ep := A.K.positive
  have cost : 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 := by unfold TenRegularCases at cases;omega
  have earlier := ten_priced_menu_excludes_eight_exit F paid ten A cases H.high
  have cap (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  obtain ⟨cap7,cap6,cap5⟩ := H.remaining_caps cap
  obtain ⟨at8,at7⟩ := H.low_cut_edge_counts cap
  change O.edgeSet.ncard=(O.induce H.high.lastCutᶜ).edgeSet.ncard+8*g+b+c at at8
  change O.edgeSet.ncard=(O.induce H.sevenCutᶜ).edgeSet.ncard+7*l+b+c+g at at7
  have short := (A.step_bounds paid ten cost).1
  have room (j:ℕ) (V:Set ↥(A.K.supportᶜ:Set F.X)) (pos:0<j)
      (low:∀x,Nat.card ((O.induce Vᶜ).neighborSet x)<j)
      (present:0<originalThresholdCount F.n j ∨ 0<originalThresholdCount F.m j) : A.steps≤V.ncard :=
    short.trans ((ten_closed_endpoint_sizes F paid ten A.K).2 V j pos low present)
  by_cases reaches:A.steps≤l
  · have bill : O.edgeSet.ncard=(O.induce H.high.lastCutᶜ).edgeSet.ncard+(7+1)*H.high.lastCut.ncard+(b+c) := by
      change O.edgeSet.ncard=_+(7+1)*g+(b+c);omega
    obtain ⟨V,num,_,low,fee⟩ := take_partial_stage_at_cap O H.high.lastCut 7 (b+c) cap7 bill H.seven H.stageSeven
      A.steps earlier.le reaches
    exact Or.inl ⟨⟨V,num,low,by simpa only [O,g,l,Nat.add_assoc] using fee⟩⟩
  · have absent : ¬(0<originalThresholdCount F.n 7 ∨ 0<originalThresholdCount F.m 7) := fun head =>
      reaches (room 7 H.sevenCut (by decide) (fun v => Nat.lt_succ_of_le (cap6 v)) head)
    have heads := strict_ten_priced_regular_heads_at_most_seven F paid ten A cases
    obtain ⟨_,i,j,_,_,red,blue,_⟩ := ten_central_peak_bounds_width F paid ten heads.1 heads.2
    have yes := (original_threshold_prefix F.n F.hn 6 i).mp red.ge
    have fill := room 6 H.sixCut (by decide) (fun v => Nat.lt_succ_of_le (cap5 v)) (Or.inl (by omega))
    have bill : O.edgeSet.ncard=(O.induce H.sevenCutᶜ).edgeSet.ncard+(6+1)*H.sevenCut.ncard+(b+c+g) := by
      change O.edgeSet.ncard=_+(6+1)*l+(b+c+g);omega
    have before : H.sevenCut.ncard≤A.steps := Nat.le_of_lt (Nat.lt_of_not_ge reaches)
    obtain ⟨V,num,_,low,fee⟩ := take_partial_stage_at_cap O H.sevenCut 6 (b+c+g) cap6 bill H.six H.stageSix
      A.steps before fill
    refine Or.inr ⟨?_,?_,⟨⟨V,num,low,by simpa only [O,g,l,Nat.add_assoc] using fee⟩⟩⟩
    · intro p;by_contra! big
      have hits := (original_threshold_prefix F.n F.hn 7 p).mp big
      exact absent (Or.inl (by omega))
    · intro p;by_contra! big
      have hits := (original_threshold_prefix F.m F.hm 7 p).mp big
      exact absent (Or.inr (by omega))
#print axioms ten_regular_lower_exit_exists
end JSP452Audit.StarHost
