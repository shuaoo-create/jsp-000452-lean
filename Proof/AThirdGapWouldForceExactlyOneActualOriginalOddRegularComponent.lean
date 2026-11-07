import NoLowThirdGapPlatformOnTheOriginalPaidExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem third_gap_requires_original_regular_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    D=H+3 → D%2=0 ∧ h=1 ∧ (oddRegularComponents F.G D).ncard=1 ∧
      ∃J:F.G.ConnectedComponent,Odd (Nat.card J.supp) ∧ (∀v∈J.supp,Nat.card (F.G.neighborSet v)=D) ∧
        ∀Q:F.G.ConnectedComponent,Q∈oddRegularComponents F.G D → Q=J := by
  intro D H h gap
  obtain ⟨K,k,c,P,live,⟨E⟩,hp,rp,sharp,_,_,_,states⟩ := third_gap_remaining_original_states F paid gap
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have credit : P.gamma h≤ -2*(P.excess:ℤ) := by
    change 8*P.gamma h+(3*(D:ℤ)+2)*P.excess+((D:ℤ)-10)*h+4*P.beta≤0 at sharp
    have a := mul_nonneg (show (0:ℤ)≤3*(D:ℤ)-14 by omega) (show (0:ℤ)≤P.excess by positivity)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-10 by omega) (show (0:ℤ)≤h by positivity)
    linarith only [a,b,sharp,show (0:ℤ)≤P.beta by positivity]
  have high := third_gap_low_impossible F paid P E live hp credit gap
  rcases states with low|⟨even,one,_,_,regular⟩
  · omega
  · obtain ⟨J,eq⟩ := Set.ncard_eq_one.mp regular
    have mem : J∈oddRegularComponents F.G D := eq.ge (Set.mem_singleton J)
    exact ⟨even,one,regular,J,mem.1,mem.2,fun Q inside => Set.mem_singleton_iff.mp (eq.le inside)⟩

#print axioms third_gap_requires_original_regular_component
end JSP452Audit.StarHost
