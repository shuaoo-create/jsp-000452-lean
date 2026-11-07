import SharpSignedOddExposure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_seven_exposure_budget (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) :
    7*(minimumExposure F.G 7:ℤ)+2 ≤ 2*(highestWidth F.n F.m F.r:ℤ)+24 := by
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤7 := (degree v).trans_eq seven
  have hi := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row degree).1
  have top : diagonal F.n F.m (F.r+2)=8 := by omega
  have net : selectorTarget F.G 7<(highestWidth F.n F.m F.r:ℤ) := by
    by_cases pos:0<selectorTarget F.G 7
    · have price := selector_positive_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r 7 F.rank
        F.row F.live le_rfl paid cap top.le pos
      rw [show 7+1=diagonal F.n F.m (F.r+2) by omega,width_at_peak F.hs F.ht F.n F.m F.hn F.hm] at price
      have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
      omega
    · omega
  change (7*(minimumExposure F.G 7:ℤ)+1)/2-12<(highestWidth F.n F.m F.r:ℤ) at net
  omega

theorem seven_pair_signed_gap {X:Type*} [Finite X] (G:SimpleGraph X) (cap:∀v,Nat.card (G.neighborSet v)≤7)
    (a b u v:ℕ) (ha:3≤a) (hb:3≤b) (sum:a+b=9) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => a)) (forest (fun _:Fin v => b)))
    (limit:minimumExposure G 7≤4) :
    ((a=4 ∧ b=5) ∨ (a=5 ∧ b=4)) ∧ u+v-1+2≤minimumExposure G 7 := by
  have cases : (a=6 ∧ b=3) ∨ (a=4 ∧ b=5) ∨ (a=5 ∧ b=4) ∨ (a=3 ∧ b=6) := by omega
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have fee := seven_signed_three_six G cap u v hu hv force
    dsimp only at fee;omega
  · have fee := seven_signed_four_five G cap u v hu hv force
    dsimp only at fee;exact ⟨Or.inl ⟨rfl,rfl⟩,by omega⟩
  · have fee := seven_signed_four_five G cap v u hv hu (forces_swap force)
    dsimp only at fee;exact ⟨Or.inr ⟨rfl,rfl⟩,by omega⟩
  · have fee := seven_signed_three_six G cap v u hv hu (forces_swap force)
    dsimp only at fee;omega

theorem strict_seven_original_peak (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (seven:diagonal F.n F.m (F.r+2)-1=7) :
    highestWidth F.n F.m F.r=1 ∧ minimumExposure F.G 7=3 ∧
    ∃(i:Fin F.s) (j:Fin F.t),i.val+j.val=F.r ∧
      ((F.n i=4 ∧ F.m j=5) ∨ (F.n i=5 ∧ F.m j=4)) ∧
      Forces F.G (forest (fun _:Fin 1 => F.n i)) (forest (fun _:Fin 1 => F.m j)) := by
  obtain ⟨_,_,_,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤7 := (degree v).trans_eq seven
  have upper := minimal_source_exposure_cap F paid
  dsimp only at upper;rw [seven] at upper
  have limit : minimumExposure F.G 7≤4 := by norm_num at upper;omega
  obtain ⟨i,j,u,v,idx,sum,ha,_,hb,_,hu,hv,_,_,width,forced,_,_⟩ := strict_actual_peak_factor_obstruction F paid
  rw [seven] at sum
  obtain ⟨shapes,gap⟩ := seven_pair_signed_gap F.G cap _ _ u v ha hb sum hu hv forced limit
  have budget := strict_seven_exposure_budget F paid seven
  have h : highestWidth F.n F.m F.r=1 := by omega
  have exposure : minimumExposure F.G 7=3 := by omega
  have uone : u=1 := by omega
  have vone : v=1 := by omega
  subst u;subst v
  exact ⟨h,exposure,i,j,idx,shapes,forced⟩

#print axioms strict_seven_exposure_budget
#print axioms seven_pair_signed_gap
#print axioms strict_seven_original_peak
end JSP452Audit.StarHost
