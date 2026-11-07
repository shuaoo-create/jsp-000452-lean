import TheOrientedUniformPeakAndItsActualOriginalFactorCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem odd_original_peak_exposure {X:Type u} [Finite X] {G:SimpleGraph X} {h p q D:ℕ}
    (peak:OriginalUniformPeak G h p q) (sum:p+q=D) (odd:p%2=1) (even:q%2=0) (large:2≤q)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) :
    h+(p-1)*((h-1)/q+1)≤minimumExposure G D ∧
    (D-1)*h≤q*minimumExposure G D := by
  obtain ⟨u,v,pu,pv,rank,force,_⟩ := peak
  let r := p/2
  let t := q/2
  have P : 2*r+1=p := by dsimp only [r];omega
  have Q : 2*t=q := by dsimp only [t];omega
  have deg : 2*(r+t)+1=D := by omega
  have typed : Forces G (forest (fun _:Fin u => 2*r+2)) (forest (fun _:Fin v => 2*t+1)) := by
    rwa [show 2*r+2=p+1 by omega,Q]
  have charge := actual_odd_sharp_signed_width G r t (by omega) (fun x => (cap x).trans_eq deg.symm) u v pu pv typed
  change u+v-1+2*r*((u+v-1-1)/(2*t)+1)≤minimumExposure G (2*(r+t)+1) at charge
  rw [rank,Q,deg,show 2*r=p-1 by omega] at charge
  let m := (h-1)/q+1
  have room : h≤m*q := by
    have quote := Nat.mod_lt (h-1) (show 0<q by omega)
    have self := Nat.mod_add_div (h-1) q
    dsimp only [m];rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm ((h-1)/q) q];omega
  have scaled := Nat.mul_le_mul_left q charge
  change q*(h+(p-1)*m)≤q*minimumExposure G D at scaled
  have use := Nat.mul_le_mul_left (p-1) room
  have eq : D-1=q+(p-1) := by omega
  refine ⟨charge,?_⟩
  rw [eq,Nat.add_mul]
  calc
    q*h+(p-1)*h ≤ q*h+(p-1)*(m*q) := Nat.add_le_add_left use _
    _ = q*(h+(p-1)*m) := by ring
    _ ≤ _ := scaled

theorem eleven_actual_peak_shapes (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eleven:diagonal F.n F.m (F.r+2)-1=11) :
    let h := highestWidth F.n F.m F.r
    let rho := minimumExposure F.G 11
    rho≤6 ∧ ((OriginalUniformPeak F.G h 3 8 ∧ h+2≤rho) ∨
      (OriginalUniformPeak F.G h 5 6 ∧ h+4≤rho)) := by
  intro h rho
  have cap (x) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq eleven
  have bill := minimal_source_exposure_cap F paid
  rw [eleven] at bill;norm_num at bill
  have limit : rho≤6 := by change minimumExposure F.G 11≤6;omega
  obtain ⟨p,q,pmin,qmin,sum,peak,odd,_,_⟩ := strict_oriented_high_peak F paid
  rw [eleven] at sum odd
  obtain ⟨op,eq⟩ := odd (by decide)
  have bound := (odd_original_peak_exposure peak sum op eq qmin cap).1
  have plain := Nat.mul_le_mul_left (p-1) (Nat.succ_le_succ (Nat.zero_le ((h-1)/q)))
  change h+(p-1)*((h-1)/q+1)≤rho at bound
  rw [Nat.mul_one] at plain
  change p-1≤(p-1)*((h-1)/q+1) at plain
  have cut : h+(p-1)≤rho := by omega
  have hp : 1≤h := by
    have v := peak;obtain ⟨u,v,pu,pv,wide,_⟩ := v;change u+v-1=h at wide;omega
  refine ⟨limit,?_⟩
  by_cases small:p=3
  · obtain rfl : p=3 := small
    obtain rfl : q=8 := by omega
    exact Or.inl ⟨peak,by omega⟩
  · obtain rfl : p=5 := by omega
    obtain rfl : q=6 := by omega
    exact Or.inr ⟨peak,by omega⟩

#print axioms odd_original_peak_exposure
#print axioms eleven_actual_peak_shapes
end JSP452Audit.StarHost
