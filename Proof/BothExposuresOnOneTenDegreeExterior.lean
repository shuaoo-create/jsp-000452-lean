import TheCompleteTenDegreeSuccessorAndItsExactCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_both_exterior_exposures (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (cost:6*highestWidth F.n F.m F.r≤13*A.K.eps+6) (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) :
    let h := highestWidth F.n F.m F.r
    let O := F.G.induce A.K.supportᶜ
    minimumExposure (O.induce H.upperᶜ) 9≤(38+2*h)/7 ∧
      minimumExposure (O.induce H.midCutᶜ) 8≤max 4 ((h-1+((38+2*h)/7-2)+16)/3) := by
  intro h O
  obtain ⟨red,blue⟩ := strict_ten_no_nine_leaf_with_regular_menu F paid ten A cost
  have second := strict_ten_second_exterior_exposure F paid ten A.K.support A.K.support_closed red blue H
  obtain ⟨I,stage,_⟩ := A.shortStage
  obtain ⟨joined,_⟩ := join_closed_degree_stages F.G A.K.support 10 A.K.support_closed I H.upper stage H.first
  have first := (strict_ten_complete_stage F paid ten _ joined).2.2.2.2.2
  rw [exposure_after_closed_stage_split F.G A.K.support A.K.support_closed I H.upper 9] at first
  change 7*(_+minimumExposure (O.induce H.upperᶜ) 9)≤38+2*h at first
  exact ⟨by omega,second⟩
#print axioms ten_both_exterior_exposures
end JSP452Audit.StarHost
