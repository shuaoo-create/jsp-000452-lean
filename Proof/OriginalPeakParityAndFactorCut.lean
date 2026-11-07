import TrueOriginalUniformFactorCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem actual_peak_parity {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (i : Fin s) (j : Fin t) (idx : i.val+j.val=r) (sum : n i+m j=D+2) (even : D%2=0) :
    n i%2=0 ∧ m j%2=0 := by
  by_contra! no
  have red : n i=2*(n i/2)+1 := by omega
  have blue : m j=2*(m j/2)+1 := by omega
  have total : D=2*(n i/2+m j/2) := by omega
  have pair := row_forces_star_pair G _ _ row i j idx
  have f : Forces G (oneStar (n i)) (oneStar (m j)) := by
    have e1 : padDemand n i.val=n i := dif_pos i.isLt
    have e2 : padDemand m j.val=m j := dif_pos j.isLt
    rw [e1,e2] at pair;exact pair
  have full : Forces G (oneStar (2*(n i/2)+1)) (oneStar (2*(m j/2)+1)) := by rwa [←red,←blue]
  exact no_odd_odd_star_corner G (n i/2) (m j/2) (fun v => (cap v).trans_eq total) full

def ActualPeakObstruction (F : StrictFamily.{u}) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  let h := highestWidth F.n F.m F.r
  ∃(i:Fin F.s) (j:Fin F.t) (u v:ℕ),
    i.val+j.val=F.r ∧ F.n i+F.m j=D+2 ∧
    3≤F.n i ∧ F.n i<D ∧ 3≤F.m j ∧ F.m j<D ∧
    0<u ∧ 0<v ∧ u≤headWidth F.n i ∧ v≤headWidth F.m j ∧ u+v-1=h ∧
    Forces F.G (forest (fun _:Fin u => F.n i)) (forest (fun _:Fin v => F.m j)) ∧
    (D%2=0 → F.n i%2=0 ∧ F.m j%2=0) ∧
    ∃S T:Set F.X,Disjoint S T ∧ (h:ℤ)≤originalFactorCut F.G (F.n i-1) (F.m j-1) S T

theorem strict_actual_peak_factor_obstruction (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    ActualPeakObstruction F := by
  unfold ActualPeakObstruction
  intro D h
  have deg : 6≤D := strict_source_degree_at_least_six F paid
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  obtain ⟨i,j,u,v,idx,eq,up,vp,ur,vr,width,forced⟩ :=
    original_highest_corner_uniform_width F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.row F.live
  have cut : F.n i+F.m j=D+2 := by dsimp only [D] at *;omega
  have nr : F.n i<D := red i
  have mb : F.m j<D := blue j
  obtain ⟨S,T,dis,fee⟩ := original_uniform_factor_cut F.G (F.n i) (F.m j) u v (F.pn i) (F.pm j) up vp
    (fun z => (cap z).trans_eq (by change D=F.n i-1+(F.m j-1);omega)) forced
  refine ⟨i,j,u,v,idx,cut,by omega,nr,by omega,mb,up,vp,ur,vr,width,forced,?_,S,T,dis,?_⟩
  · exact actual_peak_parity F.G F.n F.m F.row cap i j idx cut
  · change u+v-1=h at width;rw [←width];exact fee

#print axioms actual_peak_parity
#print axioms strict_actual_peak_factor_obstruction
end JSP452Audit.StarHost