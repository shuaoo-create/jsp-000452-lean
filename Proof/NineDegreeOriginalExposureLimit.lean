import OriginalStrictDegreeEightExcluded
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_exposure_budget (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) :
    9*(minimumExposure F.G 9:ℤ)+2≤2*(highestWidth F.n F.m F.r:ℤ)+40 := by
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have top : diagonal F.n F.m (F.r+2)=10 := by omega
  have hi := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row
    (minimal_rank_exact_source F paid).2.2.2.1).1
  have net : selectorTarget F.G 9<(highestWidth F.n F.m F.r:ℤ) := by
    by_cases pos:0<selectorTarget F.G 9
    · have price := selector_positive_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r 9 F.rank F.row
        F.live le_rfl paid cap top.le pos
      rw [show 9+1=diagonal F.n F.m (F.r+2) by omega,width_at_peak F.hs F.ht F.n F.m F.hn F.hm] at price
      have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
      omega
    · omega
  change (9*(minimumExposure F.G 9:ℤ)+1)/2-20<(highestWidth F.n F.m F.r:ℤ) at net
  omega

theorem nine_uniform_signed_alternatives {X:Type*} [Finite X] (G:SimpleGraph X) (cap:∀x,Nat.card (G.neighborSet x)≤9)
    (a b u v:ℕ) (ha:3≤a) (hb:3≤b) (sum:a+b=11) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => a)) (forest (fun _:Fin v => b))) :
    let l := u+v-1
    l+2≤minimumExposure G 9 ∧
      ((a=4 ∧ b=7) ∨ (a=7 ∧ b=4) ∨ l+4≤minimumExposure G 9) := by
  intro l
  have cases : (a=4 ∧ b=7) ∨ (a=6 ∧ b=5) ∨ (a=8 ∧ b=3) ∨ (a=7 ∧ b=4) ∨ (a=5 ∧ b=6) ∨ (a=3 ∧ b=8) := by omega
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have fee := actual_odd_sharp_signed_width G 1 3 (by decide) cap u v hu hv force
    norm_num at fee;exact ⟨by omega,Or.inl ⟨rfl,rfl⟩⟩
  · have fee := actual_odd_sharp_signed_width G 2 2 (by decide) cap u v hu hv force
    norm_num at fee;exact ⟨by omega,Or.inr (Or.inr (by omega))⟩
  · have fee := actual_odd_sharp_signed_width G 3 1 (by decide) cap u v hu hv force
    norm_num at fee;exact ⟨by omega,Or.inr (Or.inr (by omega))⟩
  · have fee := actual_odd_sharp_signed_width G 1 3 (by decide) cap v u hv hu (forces_swap force)
    norm_num at fee;exact ⟨by omega,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  · have fee := actual_odd_sharp_signed_width G 2 2 (by decide) cap v u hv hu (forces_swap force)
    norm_num at fee;exact ⟨by omega,Or.inr (Or.inr (by omega))⟩
  · have fee := actual_odd_sharp_signed_width G 3 1 (by decide) cap v u hv hu (forces_swap force)
    norm_num at fee;exact ⟨by omega,Or.inr (Or.inr (by omega))⟩

theorem strict_nine_original_peak (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (nine:diagonal F.n F.m (F.r+2)-1=9) :
    let h := highestWidth F.n F.m F.r
    let rho := minimumExposure F.G 9
    1≤h ∧ h≤2 ∧ h+2≤rho ∧ rho≤4 ∧ ∃(i:Fin F.s) (j:Fin F.t) (u v:ℕ),
      i.val+j.val=F.r ∧ ((F.n i=4 ∧ F.m j=7) ∨ (F.n i=7 ∧ F.m j=4)) ∧
      0<u ∧ 0<v ∧ u+v-1=h ∧ Forces F.G (forest (fun _:Fin u => F.n i)) (forest (fun _:Fin v => F.m j)) := by
  intro h rho
  have cap (x:F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  obtain ⟨i,j,u,v,idx,sum,ha,_,hb,_,hu,hv,_,_,width,force,_,_⟩ := strict_actual_peak_factor_obstruction F paid
  rw [nine] at sum
  obtain ⟨bound,shape⟩ := nine_uniform_signed_alternatives F.G cap _ _ u v ha hb sum hu hv force
  change u+v-1=h at width
  rw [width] at bound shape
  change h+2≤rho at bound
  have fee := strict_nine_exposure_budget F paid nine
  change 9*(rho:ℤ)+2≤2*(h:ℤ)+40 at fee
  have hp : 1≤h := by omega
  have maxR : rho≤4 := by omega
  have pair : (F.n i=4 ∧ F.m j=7) ∨ (F.n i=7 ∧ F.m j=4) := by
    rcases shape with a|b|impossible;exact Or.inl a;exact Or.inr b;change h+4≤rho at impossible;omega
  exact ⟨hp,by omega,bound,maxR,i,j,u,v,idx,pair,hu,hv,width,force⟩

#print axioms strict_nine_exposure_budget
#print axioms nine_uniform_signed_alternatives
#print axioms strict_nine_original_peak
end JSP452Audit.StarHost
