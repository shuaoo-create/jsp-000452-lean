import OriginalFailureTwoRemainingRegimes
namespace JSP452Audit.StarHost

/-- A column exceeding both monochrome sources has an actual attaining
rectangle; each available pure axis ends before its right endpoint. -/
theorem mixed_actual_pair {s t k : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : k<s+t-1) (gap : monochromeHeight n m k<diagonal n m (k+2)) :
    let h := diagonal n m (k+2)
    ∃x y, 2≤x ∧ 2≤y ∧ x+y-1=h ∧ 0<originalThresholdCount n x ∧ 0<originalThresholdCount m y ∧
      (0<originalThresholdCount n h → originalThresholdCount n h+t<originalThresholdCount n x+originalThresholdCount m y) ∧
      (0<originalThresholdCount m h → s+originalThresholdCount m h<originalThresholdCount n x+originalThresholdCount m y) := by
  intro h
  obtain ⟨i,j,idx,att⟩ := diagonal_attained n m hs ht k live
  let a : Fin s := ⟨k-(t-1),by omega⟩
  let b : Fin t := ⟨k-(s-1),by omega⟩
  have da : padDemand n (k-(t-1))=n a := dif_pos a.isLt
  have db : padDemand m (k-(s-1))=m b := dif_pos b.isLt
  unfold monochromeHeight at gap;rw [da,db] at gap
  change max (n a) (m b)<h at gap
  change h=n i+m j-1 at att
  have ni := hn (show a ≤ i from by change k-(t-1)≤ i.val;have := j.isLt;omega)
  have mj := hm (show b ≤ j from by change k-(s-1)≤ j.val;have := i.isLt;omega)
  have ncut := (original_threshold_prefix n hn (n i) i).1 le_rfl
  have mcut := (original_threshold_prefix m hm (m j) j).1 le_rfl
  refine ⟨n i,m j,by omega,by omega,att.symm,by omega,by omega,?_,?_⟩
  · intro pos
    have endAt : originalThresholdCount n h≤a.val := by
      by_contra! more;have := (original_threshold_prefix n hn h a).2 more;omega
    change originalThresholdCount n h≤k-(t-1) at endAt;omega
  · intro pos
    have endAt : originalThresholdCount m h≤b.val := by
      by_contra! more;have := (original_threshold_prefix m hm h b).2 more;omega
    change originalThresholdCount m h≤k-(s-1) at endAt;omega

open SimpleGraph
universe u

def FullMixedBoundary {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht:0<t) (r D μ : ℕ) : Prop :=
  ∃h y, 2≤y ∧ y+1=h ∧ h≤D ∧ 0<originalThresholdCount m y ∧
    originalThresholdCount n h+t<originalThresholdCount n 2+originalThresholdCount m y ∧
    (h≤m ⟨0,ht⟩ → s+originalThresholdCount m h<originalThresholdCount n 2+originalThresholdCount m y) ∧
    (originalThresholdCount n 2≤μ → y=m ⟨0,ht⟩ ∧ h=m ⟨0,ht⟩+1)

theorem full_head_forces_mixed_boundary {s t r D : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1) (rho μ : ℕ) (width : highestWidth n m r≤rho)
    (guard : rho+1≤t-(r+2*(∑i,(n i-1)/2))) (largeS : μ+r+rho<s)
    (mixed : ∃z,z<rowCount s t r ∧ monochromeHeight n m (r+z)<diagonal n m (r+z+2) ∧
      diagonal n m (r+z+2)<diagonal n m (r+2)) : FullMixedBoundary n m ht r D μ := by
  obtain ⟨z,legal,gap,below⟩ := mixed
  let H := diagonal n m (r+z+2)
  have bound : H≤D := by change diagonal n m (r+z+2)≤D;omega
  obtain ⟨x,y,xhi,yhi,height,px,py,red,blue⟩ := mixed_actual_pair hs ht n m hn hm pn pm
    (by dsimp [rowCount] at legal;omega) gap
  have redH : 0<originalThresholdCount n H := (original_threshold_prefix n hn H ⟨0,hs⟩).1 (bound.trans_eq head.symm)
  have win := red redH
  change originalThresholdCount n H+t<originalThresholdCount n x+originalThresholdCount m y at win
  have P := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have mono := threshold_anti_height m yhi
  have posB : 0<originalThresholdCount m 2 := py.trans_le mono
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by omega) P posB
  have eq := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at eq;rw [eq] at rect
  have g2 : originalThresholdCount m 2≤r+rho := by omega
  have xe : x=2 := by
    by_contra ne
    have lo := half_extra_pays_large_threshold n (by omega : 3≤x)
    omega
  subst x
  have hEq : y+1=H := by change 2+y-1=H at height;omega
  have next (bhigh:H≤m ⟨0,ht⟩) : s+originalThresholdCount m H<originalThresholdCount n 2+originalThresholdCount m y :=
    blue ((original_threshold_prefix m hm H ⟨0,ht⟩).1 bhigh)
  refine ⟨H,y,yhi,hEq,bound,py,win,next,?_⟩
  intro limited
  have maxB := (original_threshold_prefix m hm y ⟨0,ht⟩).2 py
  have final : y=m ⟨0,ht⟩ := by
    by_contra ne
    have atH := next (by omega)
    omega
  exact ⟨final,by omega⟩

#print axioms mixed_actual_pair
#print axioms full_head_forces_mixed_boundary
end JSP452Audit.StarHost
