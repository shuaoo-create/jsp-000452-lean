import SingleSixStageUniformExposureCap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem four_bounded_exact_six_head {X:Type*} [Finite X] {s t r:ℕ} (G:SimpleGraph X)
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀i,1≤m i) (headN:∀i,n i≤4) (headM:∀j,m j≤4)
    (live:0<rowCount s t r) (row:ForcingRow G s t (padDemand n) (padDemand m) r)
    (top:diagonal n m (r+2)=6) (cap:∀v,Nat.card (G.neighborSet v)≤5) :
    let l := highestWidth n m r
    l+2*((l+1)/2)≤minimumExposure G 5 := by
  intro l
  obtain ⟨i,j,u,v,_,peak,hu,hv,_,_,wide,force⟩ := original_highest_corner_uniform_width hs ht n m hn hm pn pm G row live
  rw [top] at peak
  have hi := headN i
  have hj := headM j
  have cases : (n i=4 ∧ m j=3) ∨ (n i=3 ∧ m j=4) := by omega
  rcases cases with ⟨a,b⟩|⟨a,b⟩
  · rw [a,b] at force
    have bound := actual_five_sharp_signed_width G cap u v hu hv force
    rwa [wide] at bound
  · rw [a,b] at force
    have bound := actual_five_sharp_signed_width G cap v u hv hu (forces_swap force)
    rwa [Nat.add_comm v u,wide] at bound

theorem strict_single_six_no_five_rigidity (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4)
    (I:Set F.X) (stage:CompleteDegreeStage F.G 6 I) :
    I.ncard=widthAt F.n F.m F.r 6 ∧ minimumExposure (F.G.induce Iᶜ) 5≤2 := by
  let L := widthAt F.n F.m F.r 6
  let k := I.ncard
  let Y := F.G.induce Iᶜ
  obtain ⟨le,_,upper⟩ := strict_single_six_stage_caps F paid six I stage
  change k≤L at le
  change 5*minimumExposure Y 5≤2*(L-k)+12 at upper
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq six
  obtain ⟨gone,_,row⟩ := original_stage_width_and_cost F.G F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row
    (by decide : 0<6) cap I stage
  have eq : k=L := by
    by_contra diff
    obtain ⟨live,top,wide⟩ := shifted_live_six_has_exact_head F.hs F.ht F.n F.m F.hn F.hm gone (by change k<L;omega)
    have bound (v:↥(Iᶜ:Set F.X)) : Nat.card (Y.neighborSet v)≤5 := by
      have reduced := complete_stage_lowers_cap F.G 6 I cap stage v;change Nat.card (Y.neighborSet v)<6 at reduced;omega
    have lower := four_bounded_exact_six_head Y F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm red blue live row top bound
    rw [wide] at lower
    change (L-k)+2*((L-k+1)/2)≤minimumExposure Y 5 at lower
    clear * - upper lower le diff
    omega
  exact ⟨eq,by change minimumExposure Y 5≤2;omega⟩

#print axioms four_bounded_exact_six_head
#print axioms strict_single_six_no_five_rigidity
end JSP452Audit.StarHost
