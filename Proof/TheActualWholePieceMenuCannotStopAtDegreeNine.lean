import NineDegreeExposureAfterPayingTheTruePortShortfall
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_port_fee_covers_first_exposure {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ}
    (W:TenPortSupport G K h) (pos:1≤h) (narrow:h≤2) (cap:∀v,Nat.card (G.neighborSet v)≤10) :
    h+(38+2*h+2*W.seedLoss)/7≤W.fee+W.targetPorts := by
  have data := W.size_and_fee pos
  have small := (W.seed_loss_at_most_one cap).2
  omega

theorem ten_port_steps_outlast_nine (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r)) (narrow:highestWidth F.n F.m F.r≤2)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (B:Set ↥(W.supportᶜ:Set F.X)) (first:CompleteDegreeStage W.outside 10 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage (W.outside.induce Bᶜ) 9 C) : B.ncard+C.ncard<W.steps F.r := by
  by_contra! fit
  obtain ⟨I,inner⟩ := complete_degree_stage_exists (F.G.induce W.available) 10
  have bound := (ten_port_first_stage_exposure F paid ten W length I inner B first).2.2.2
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have fee := ten_port_fee_covers_first_exposure W (strict_ten_inventory F paid ten).1 narrow cap
  have price := (ten_port_first_two_stage_cost F paid ten W length B first C second fit).1
  have out := ten_port_steps_outlast_ten F paid ten W length B first
  rw [min_eq_right out.le] at price
  omega

#print axioms ten_port_fee_covers_first_exposure
#print axioms ten_port_steps_outlast_nine
end JSP452Audit.StarHost
