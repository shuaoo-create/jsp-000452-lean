import VolumeAndSlotsAtTwoAndThreeLeavesOnTheActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_exterior_stock (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ} (W:TenPortSupport F.G K h)
    (deep:h+3≤F.rank-matchingEdges F.G) (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t) :
    let d := F.rank-W.rank-matchingEdges W.outside
    W.rank+F.r+2*d≤min F.s F.t ∧
      ∀(V:Set ↥(W.supportᶜ:Set F.X)) (H:ℕ),0<H →
      (∀v,Nat.card ((W.outside.induce Vᶜ).neighborSet v)<H) →
      (0<originalThresholdCount F.n H ∨ 0<originalThresholdCount F.m H) → 2*d≤V.ncard := by
  intro d
  obtain ⟨pos,_,pa,pb,na,mb,ea,eb⟩ := ten_port_exterior_matching_endpoints F W deep length
  change h+1≤d at pos
  change 2*(d+_)≤F.t-F.r-W.rank at ea
  change 2*(d+_)≤F.s-F.r-W.rank at eb
  refine ⟨by omega,?_⟩
  intro V H live low head
  let p := H-1
  have cap (v) : Nat.card ((W.outside.induce Vᶜ).neighborSet v)≤p := by have := low v;dsimp only [p];omega
  have high : p+1=H := by dsimp only [p];omega
  rcases head with red|blue
  · have result := endpoint_stage_inventory W.outside F.hs F.n F.pn na (by omega : 0<d) (by omega) pa V cap (high.symm ▸ red)
    rw [high] at result;omega
  · have result := endpoint_stage_inventory W.outside F.ht F.m F.pm mb (by omega : 0<d) (by omega) pb V cap (high.symm ▸ blue)
    rw [high] at result;omega

theorem ten_eight_leaf_support_stock (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (narrow:highestWidth F.n F.m F.r≤2) (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (red:∀i,F.n i≤8) (blue:∀i,F.m i≤8) :
    W.half<2*(F.rank-W.rank-matchingEdges W.outside) := by
  have volume := (ten_port_volume_two_three F paid ten W deep length).2 red blue
  have code := (W.size_and_fee (strict_ten_inventory F paid ten).1).2.2.1
  omega

#print axioms ten_port_exterior_stock
#print axioms ten_eight_leaf_support_stock
end JSP452Audit.StarHost
