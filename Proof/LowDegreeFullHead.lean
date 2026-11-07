import EvenColourCornerObstruction
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

theorem no_odd_odd_attaining_pair {s t r D : ℕ} (G : SimpleGraph X)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (i : Fin s) (j : Fin t) (indices : i.val+j.val=r)
    (bound : n i+m j=D+2) (oi : Odd (n i)) (oj : Odd (m j)) : False := by
  obtain ⟨u,hu⟩ := oi
  obtain ⟨v,hv⟩ := oj
  have red : n i=2*u+1 := by omega
  have blue : m j=2*v+1 := by omega
  have deg : D=2*(u+v) := by omega
  have force := row_forces_star_pair G _ _ row i j indices
  rw [show padDemand n i.val=n i from dif_pos i.isLt,show padDemand m j.val=m j from dif_pos j.isLt,red,blue] at force
  exact no_odd_odd_star_corner G u v (deg ▸ cap) force

theorem low_degree_forces_head_at_cap (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (low : diagonal F.n F.m (F.r+2)-1≤4) :
    let D := diagonal F.n F.m (F.r+2)-1
    F.n ⟨0,F.hs⟩=D ∨ F.m ⟨0,F.ht⟩=D := by
  intro D
  have lo : 3≤D := strict_source_degree_at_least_three F paid
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  obtain ⟨redCap,blueCap⟩ := minimal_original_head_cap F paid
  by_contra! below
  have red : F.n ⟨0,F.hs⟩<D := lt_of_le_of_ne (redCap _) below.1
  have blue : F.m ⟨0,F.ht⟩<D := lt_of_le_of_ne (blueCap _) below.2
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨i,j,idx,attain,_⟩ := highest_column_head_pair F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r F.live
  have ni := F.hn (show (⟨0,F.hs⟩ : Fin F.s)≤ i from Nat.zero_le _)
  have mj := F.hm (show (⟨0,F.ht⟩ : Fin F.t)≤ j from Nat.zero_le _)
  change D≤4 at low
  have i3 : F.n i=3 := by omega
  have j3 : F.m j=3 := by omega
  exact no_odd_odd_attaining_pair F.G F.n F.m F.row cap i j idx (by omega)
    (by rw [i3];decide) (by rw [j3];decide)

#print axioms no_odd_odd_attaining_pair
#print axioms low_degree_forces_head_at_cap
end JSP452Audit.StarHost
