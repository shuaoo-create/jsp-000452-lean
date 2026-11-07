import EightDegreeExposureWithTheRecordedPortLoss
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_port_second_stage_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r)) (narrow:highestWidth F.n F.m F.r≤2)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (red:∀i,F.n i≤8) (blue:∀j,F.m j≤8) (H:ThreeDegreeStages W.outside 8) :
    minimumExposure (W.outside.induce H.upperᶜ) 9≤6 ∧ minimumExposure (W.outside.induce H.midCutᶜ) 8≤7 := by
  let A := F.G.induce W.available
  let O := W.outside
  let h := highestWidth F.n F.m F.r
  let L := widthAt F.n F.m F.r 10
  obtain ⟨I,first⟩ := complete_degree_stage_exists A 10
  obtain ⟨J,second⟩ := complete_degree_stage_exists (A.induce Iᶜ) 9
  let P := nestedRemoved I J
  let B := H.midCut
  let S := W.spent I H.upper
  let T := W.spent P B
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have innerCap (x:W.available) := (induced_neighbor_count_le F.G W.available x).trans (cap x.val)
  have outerCap (x:↥(W.supportᶜ:Set F.X)) := (induced_neighbor_count_le F.G W.supportᶜ x).trans (cap x.val)
  obtain ⟨loss,_,cost₁,limit₁⟩ := W.first_reduction cap I first H.upper H.first
  obtain ⟨fit,low,outer,_⟩ := ten_port_first_stage_exposure F paid ten W length I first H.upper H.first
  have height := (ten_costed_first_exposure F paid ten S W.seedLoss limit₁ cost₁ fit).1
  have pos := (strict_ten_inventory F paid ten).1
  have signed := ten_signed_port_original_stage F paid ten red blue S limit₁
  change L-S.ncard≤minimumExposure (F.G.induce Sᶜ) 9-2 at signed
  change minimumExposure (F.G.induce Sᶜ) 9≤(38+2*h+2*W.seedLoss)/7 at low
  change minimumExposure (W.outside.induce H.upperᶜ) 9≤(38+2*h+2*W.seedLoss)/7 at outer
  have firstN := W.spent_count I H.upper
  change S.ncard=_ at firstN
  have secondN := W.spent_count P B
  change T.ncard=_ at secondN
  obtain ⟨left,lcap⟩ := consecutive_ten_nine_account A innerCap I J first second
  obtain ⟨right,rcap⟩ := consecutive_ten_nine_account O outerCap H.upper H.middle H.first H.second
  change A.edgeSet.ncard=(A.induce Pᶜ).edgeSet.ncard+9*P.ncard+I.ncard at left
  change O.edgeSet.ncard=(O.induce Bᶜ).edgeSet.ncard+9*B.ncard+H.upper.ncard at right
  have base := W.seed_edge_split cap
  change F.G.edgeSet.ncard+W.seedLoss=A.edgeSet.ncard+O.edgeSet.ncard+10*W.innerTips.ncard at base
  have endE := W.spent_edges P B
  change (F.G.induce Tᶜ).edgeSet.ncard=(A.induce Pᶜ).edgeSet.ncard+(O.induce Bᶜ).edgeSet.ncard at endE
  have money : F.G.edgeSet.ncard=(F.G.induce Tᶜ).edgeSet.ncard+9*T.ncard+(S.ncard-W.seedLoss) := by
    change h≤S.ncard at height;change 1≤h at pos;omega
  have limit := W.spent_cap P B 8 lcap rcap
  change h≤2 at narrow
  have bound := ten_costed_eight_with_explicit_loss F paid ten T (S.ncard-W.seedLoss) 5 limit money
    (by change L-(S.ncard-W.seedLoss)≤5;omega)
  change minimumExposure (F.G.induce Tᶜ) 8≤max 4 ((h-1+5+16)/3) at bound
  have transfer := W.paid_cut_exposure P B 8
  change minimumExposure (W.outside.induce H.midCutᶜ) 8≤minimumExposure (F.G.induce Tᶜ) 8 at transfer
  omega

#print axioms ten_port_second_stage_exposure
end JSP452Audit.StarHost
