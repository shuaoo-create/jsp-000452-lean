import ThreeCutsOfOneOriginalTenDegreeCertificate
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_cut_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 10).ncard
    let rho := minimumExposure F.G 10
    2*h≤rho+c ∧ (rho=6 → c=6 ∧ 5≤h) ∧ (rho=5 → 3≤c) ∧
      (c≤2 → rho≤4) ∧ (3≤c → h≤c) := by
  intro h c rho
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤10 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  obtain ⟨hp,upper,comp,lim,tally,_,_⟩ := strict_ten_inventory F paid ten
  change 1≤h at hp
  change h≤rho at upper
  change c≤rho at comp
  change rho≤6 at lim
  change 5*rho+1≤h+20+c at tally
  rcases strict_ten_balanced_or_outer F paid ten with mid|⟨S,T,dis,fee⟩
  · change h≤c at mid
    omega
  · obtain ⟨e,m,b,d⟩ := three_prices_of_ten_cut F.G cap S T dis
    change (h:ℤ)≤originalFactorCut F.G 3 7 S T at fee
    change _≤(rho:ℤ) at b
    change _≤(c:ℤ) at d
    omega

theorem strict_ten_excess_width_cut (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10)
    (excess:(oddRegularComponents F.G 10).ncard<highestWidth F.n F.m F.r) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 10).ncard
    let rho := minimumExposure F.G 10
    c≤1 ∧ h≤2 ∧ h+2≤rho ∧ rho≤4 ∧
      ∃S T:Set F.X,Disjoint S T ∧ S.ncard=T.ncard+1 ∧
        (h:ℤ)≤originalFactorCut F.G 3 7 S T ∧ originalFactorCut F.G 3 7 S T≤2 ∧
        originalFactorCut F.G 1 9 S T=originalFactorCut F.G 3 7 S T+2 ∧
        originalFactorCut F.G 5 5 S T=originalFactorCut F.G 3 7 S T-2 := by
  intro h c rho
  change c<h at excess
  obtain ⟨_,_,_,small,many⟩ := strict_ten_cut_inventory F paid ten
  change c≤2 → rho≤4 at small
  change 3≤c → h≤c at many
  have lim : rho≤4 := small (by omega)
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤10 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  rcases strict_ten_balanced_or_outer F paid ten with mid|⟨S,T,dis,fee⟩
  · change h≤c at mid
    omega
  · obtain ⟨e,m,b,d⟩ := three_prices_of_ten_cut F.G cap S T dis
    change (h:ℤ)≤originalFactorCut F.G 3 7 S T at fee
    change _≤(rho:ℤ) at b
    change _≤(c:ℤ) at d
    exact ⟨by omega,by omega,by omega,lim,S,T,dis,by omega,fee,by omega,by omega,by omega⟩

#print axioms strict_ten_cut_inventory
#print axioms strict_ten_excess_width_cut
end JSP452Audit.StarHost
