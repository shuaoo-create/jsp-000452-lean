import FullLastBoundaryMissingPrefix
namespace JSP452Audit.StarHost

theorem full_last_all_winners_two_head {s t r D μ : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 6≤D)
    (head : n ⟨0,hs⟩=D) (blue : m ⟨0,ht⟩=D-1) (top : diagonal n m (r+2)=D+1) (live : 0<rowCount s t r)
    (before : r<t) (few : originalThresholdCount n 2≤μ) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t)
    (trigger : FullMixedBoundary n m ht r D μ) : TwoHeadTopBoundary n m ht r D := by
  obtain ⟨j,y,lo,level,_,yp,over,overB,rest⟩ := trigger
  obtain ⟨yb,jb⟩ := rest few
  have y0 : y=D-1 := yb.trans blue
  have j0 : j=D := by omega
  rw [j0,y0] at over overB
  rw [y0] at yp
  have rp := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (show 2≤n ⟨0,hs⟩ by omega)
  have present := actual_height_positive n m live top D (by omega)
  have eq := strict_mixed_layer_exact hs ht n m hn hm pn pm (by omega : 2≤D-1) (by omega : D-1+1=D) present before budget over overB rp yp
  refine ⟨blue,⟨by omega,by omega,by omega,rp,yp,eq⟩,?_⟩
  intro x y win
  obtain ⟨px,py,height,red,opp,winner⟩ := win
  have upper := (original_threshold_prefix m hm y ⟨0,ht⟩).2 opp
  have ex : x=2 := by
    by_contra no
    by_cases unit : y=1
    · have xx : x=D := by omega
      rw [unit,xx,original_threshold_one m pm] at winner;omega
    · have large : 3≤x := by omega
      have half := half_extra_pays_large_threshold n large
      have mono := threshold_anti_height m (by omega : 2≤y);omega
  exact ⟨ex,by omega⟩

#print axioms full_last_all_winners_two_head
end JSP452Audit.StarHost