import GeneralEvenPositiveWeightCeiling
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_eight_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 8).ncard
    let rho := minimumExposure F.G 8
    1≤h ∧ h≤rho ∧ c≤rho ∧ rho≤5 ∧ 4*rho+1≤h+12+c ∧
      (rho=5 → 4≤h ∧ 4≤c) ∧ (c=0 → rho≤3) := by
  intro h c rho
  have exp := strict_even_exposure_inventory F paid 4 (by decide) eight
  change 4*(rho:ℤ)≤(h:ℤ)-1+12+(c:ℤ) at exp
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have limits := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  rw [eight] at limits
  change 1≤h ∧ h≤rho at limits
  have comp : c≤rho := odd_regular_count_le_exposure F.G 8
  omega

theorem strict_eight_true_factor_peak (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) :
    let h := highestWidth F.n F.m F.r
    ∃(i:Fin F.s) (j:Fin F.t) (u v:ℕ),i.val+j.val=F.r ∧ u+v-1=h ∧
      ((F.n i=4 ∧ F.m j=6) ∨ (F.n i=6 ∧ F.m j=4)) ∧ 0<u ∧ 0<v ∧
      Forces F.G (forest (fun _:Fin u => F.n i)) (forest (fun _:Fin v => F.m j)) ∧
      ∃S T:Set F.X,Disjoint S T ∧ (h:ℤ)≤originalFactorCut F.G (F.n i-1) (F.m j-1) S T := by
  intro h
  obtain ⟨i,j,u,v,idx,sum,lo,hi,lo',hi',up,vp,_,_,width,force,parity,S,T,apart,score⟩ := strict_actual_peak_factor_obstruction F paid
  rw [eight] at sum hi hi' parity
  obtain ⟨red,blue⟩ := parity (by decide)
  exact ⟨i,j,u,v,idx,width,by omega,up,vp,force,S,T,apart,score⟩

#print axioms strict_eight_inventory
#print axioms strict_eight_true_factor_peak
end JSP452Audit.StarHost
