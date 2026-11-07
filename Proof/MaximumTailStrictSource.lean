import MaximumTailDiagonalProfile
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem retained_maximum_corner {s t r : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (peak : diagonal n m (r+2)=n ⟨0,hs⟩+m ⟨0,ht⟩-1) :
    ∃i:Fin s,∃j:Fin t,i.val+j.val=r ∧ n i=n ⟨0,hs⟩ ∧ m j=m ⟨0,ht⟩ := by
  obtain ⟨i,j,idx,val⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  have ni := hn (show (⟨0,hs⟩ : Fin s)≤ i by exact Nat.zero_le _)
  have mj := hm (show (⟨0,ht⟩ : Fin t)≤j by exact Nat.zero_le _)
  have pi := pn i;have pj := pm j
  exact ⟨i,j,idx,by omega,by omega⟩

noncomputable def maximumTailSource (F : StrictFamily.{u}) (i : Fin F.s) (j : Fin F.t)
    (cut : i.val+j.val=F.r) (red : ∀z,F.n z≤F.n i) (blue : ∀z,F.m z≤F.m j) : StrictFamily.{u} where
  X := F.X
  G := F.G
  s := F.s-i.val
  t := F.t-j.val
  r := 0
  n := originalTail F.n i
  m := originalTail F.m j
  hs := by have := i.isLt;omega
  ht := by have := j.isLt;omega
  hn := (tail_sorted_positive F.n F.hn F.pn i).1
  hm := (tail_sorted_positive F.m F.hm F.pm j).1
  pn := (tail_sorted_positive F.n F.hn F.pn i).2
  pm := (tail_sorted_positive F.m F.hm F.pm j).2
  live := (maximum_tail_rank i j cut).symm ▸ F.live
  row := (finite_targets_row_zero F.G (by have := i.isLt;omega) (by have := j.isLt;omega) _ _).2
    (forces_original_tails F.G F.n F.m F.row i j cut)
  strict := by
    have energies := (maximum_tail_full_profile F.n F.m F.hn F.hm i j cut red blue).1 0
    rw [Nat.add_zero] at energies
    rw [energies];exact F.strict

theorem maximum_tail_source_minima (F : StrictFamily.{u}) (i : Fin F.s) (j : Fin F.t)
    (cut : i.val+j.val=F.r) (red : ∀z,F.n z≤F.n i) (blue : ∀z,F.m z≤F.m j)
    (paid : AllSmallerPaid.{u} F.rank) :
    let T := maximumTailSource F i j cut red blue
    T.r=0 ∧ T.rank=F.rank ∧ T.edges=F.edges ∧ T.order=F.order ∧ AllSmallerPaid.{u} T.rank ∧
    T.n ⟨0,T.hs⟩=F.n i ∧ T.m ⟨0,T.ht⟩=F.m j ∧
    (∀z,rowEnergy T.n T.m z=rowEnergy F.n F.m (F.r+z)) ∧ highestWidth T.n T.m 0=highestWidth F.n F.m F.r := by
  intro T
  have rk : T.rank=F.rank := maximum_tail_rank i j cut
  have account := maximum_tail_full_profile F.n F.m F.hn F.hm i j cut red blue
  refine ⟨rfl,rk,rfl,rfl,rk.symm ▸ paid,?_,?_,account⟩
  · change padDemand F.n (i.val+0)=F.n i
    simp [padDemand,i.isLt]
  · change padDemand F.m (j.val+0)=F.m j
    simp [padDemand,j.isLt]

#print axioms retained_maximum_corner
#print axioms maximumTailSource
#print axioms maximum_tail_source_minima
end JSP452Audit.StarHost