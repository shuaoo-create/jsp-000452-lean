import NarrowedEightDegreeOriginalCases
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem tight_eight_cut_if_no_odd_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (none:(oddRegularComponents F.G 8).ncard=0) :
    ∃S T:Set F.X,Disjoint S T ∧ originalFactorCut F.G 3 5 S T=1 ∧
      (uniformOddPieces F.G 3 5 S T).ncard+crossCount F.G T S=4*S.ncard+4*T.ncard := by
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤8 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq eight
  obtain ⟨h,rho⟩ := (eight_original_interpolated_cases F paid eight).2.2.2.1 none
  obtain ⟨i,j,u,v,_,wide,shape,up,vp,force,_⟩ := strict_eight_true_factor_peak F paid eight
  have cut : ∃S T:Set F.X,Disjoint S T ∧ 1≤originalFactorCut F.G 3 5 S T := by
    rw [h] at wide
    rcases shape with ⟨a,b⟩|⟨a,b⟩ <;> rw [a,b] at force
    · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 6 u v (by decide) (by decide) up vp cap force
      rw [wide] at fee;exact ⟨S,T,dis,fee⟩
    · obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G 4 6 v u (by decide) (by decide) vp up cap (forces_swap force)
      rw [Nat.add_comm v u,wide] at fee;exact ⟨S,T,dis,fee⟩
  obtain ⟨S,T,apart,fee⟩ := cut
  have e := matching_endpoint_cut F.G 8 (by decide) cap S T apart
  rw [rho,uniform_factor_cut_on_original] at e
  have same := same_odd_capacity_piece_family F.G 3 5 1 7 (by decide) (by decide) (by decide) S T
  change ((uniformOddPieces F.G 1 7 S T).ncard:ℤ)+(crossCount F.G T S:ℤ)-1*(S.ncard:ℤ)-7*(T.ncard:ℤ)≤3 at e
  rw [←same] at e
  have mid := half_cut_for_same_pieces F.G 4 3 5 (by decide) cap S T apart
  rw [none,Nat.add_zero] at mid
  refine ⟨S,T,apart,?_,?_⟩ <;> rw [uniform_factor_cut_on_original] at fee
  · rw [uniform_factor_cut_on_original];omega
  · omega

#print axioms tight_eight_cut_if_no_odd_component
end JSP452Audit.StarHost
