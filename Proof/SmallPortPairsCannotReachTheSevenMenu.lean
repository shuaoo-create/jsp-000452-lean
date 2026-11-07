import ElevenFullVerticesSurviveThePortErasure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem first_nine_stage_needs_two_vertices {X : Type u} [Finite X] (G : SimpleGraph X)
    (U B : Set X) (many : 11≤U.ncard) (full : ∀x∈U,Nat.card (G.neighborSet x)=9)
    (stage : CompleteDegreeStage G 9 B) : 2≤B.ncard := by
  classical
  by_contra! small
  have nonempty : U.Nonempty := (Set.ncard_pos U.toFinite).mp (by omega)
  obtain ⟨x,xin⟩ := nonempty
  have point : B.Nonempty := (stage.2.2 x (full x xin)).elim (fun h => ⟨x,h⟩) (fun ⟨b,h,_⟩ => ⟨b,h⟩)
  obtain ⟨b,bin⟩ := point
  have unique := (Set.ncard_le_one (s:=B)).mp (show B.ncard≤1 by omega)
  have covered : U⊆insert b (G.neighborSet b) := by
    intro v hv
    rcases stage.2.2 v (full v hv) with inside|⟨y,yi,e⟩
    · exact Or.inl (unique _ inside _ bin)
    · have eq : y=b := unique _ yi _ bin
      exact Or.inr (show G.Adj b v from eq ▸ e.symm)
  have count := Set.ncard_le_ncard covered
  have cost := Set.ncard_insert_le b (G.neighborSet b)
  have one : (G.neighborSet b).ncard=9 := stage.2.1 b bin
  omega

theorem strict_nine_two_long_capacity_is_large (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    2≤H.upper.ncard ∧ 6≤portMenuGap R.capacity-(F.r+1) ∧ 14≤R.totalCapacity := by
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  obtain ⟨U,many,full⟩ := R.eleven_spare_full_vertices cap
  have two := first_nine_stage_needs_two_vertices R.erased U H.upper many full H.first
  have stage := strict_nine_actual_stage_inventory F paid nine R H
  obtain ⟨short,fits,_⟩ := strict_nine_final_seven_menu F paid nine R long H
  have debt := stage.2.2.2 short fits
  let k := portMenuGap R.capacity-(F.r+1)
  have count := nested_removed_card H.upper H.middle
  change H.midCut.ncard=H.upper.ncard+H.middle.ncard at count
  change H.upper.ncard+H.midCut.ncard+9+R.portCount≤2*k+highestWidth F.n F.m F.r at debt
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have large : 6≤k := by omega
  have a := (R.inner 0).2
  have b := (R.inner 1).2
  change 5≤R.capacity 0 at a;change 5≤R.capacity 1 at b
  refine ⟨two,large,?_⟩
  change 14≤R.capacity 0+R.capacity 1
  change 6≤max (min (R.capacity 0) (R.capacity 1)) (max (R.capacity 0) (R.capacity 1)-min (R.capacity 0) (R.capacity 1))-(F.r+1) at large
  omega

#print axioms first_nine_stage_needs_two_vertices
#print axioms strict_nine_two_long_capacity_is_large
end JSP452Audit.StarHost
