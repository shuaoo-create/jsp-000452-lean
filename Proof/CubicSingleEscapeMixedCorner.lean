import StrictMixedColumnObstruction
import CubicOriginalHeightProfile
namespace JSP452Audit.StarHost
universe u

/-- If a mixed column lies below a cubic peak, only 2 against 2 can
attain it. The pure red 3-axis has already ended at that column. -/
theorem cubic_mixed_corner_length {s t r z : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (head : n ⟨0,hs⟩=3)
    (live : r+z<s+t-1) (below : diagonal n m (r+z+2)<4)
    (mixed : monochromeHeight n m (r+z)<diagonal n m (r+z+2)) :
    ∃i:Fin s,∃j:Fin t,i.val+j.val=r+z ∧ n i=2 ∧ m j=2 ∧
      originalThresholdCount n 3+t<originalThresholdCount n 2+originalThresholdCount m 2 := by
  obtain ⟨i,j,idx,win⟩ := diagonal_attained n m hs ht (r+z) live
  let a : Fin s := ⟨r+z-(t-1),by omega⟩
  let b : Fin t := ⟨r+z-(s-1),by omega⟩
  have da : padDemand n (r+z-(t-1))=n a := dif_pos a.isLt
  have db : padDemand m (r+z-(s-1))=m b := dif_pos b.isLt
  unfold monochromeHeight at mixed
  rw [da,db] at mixed
  have ar : a ≤ i := by change r+z-(t-1) ≤ i.val;have := j.isLt;omega
  have br : b ≤ j := by change r+z-(s-1) ≤ j.val;have := i.isLt;omega
  have nr := hn ar
  have mb := hm br
  have pair : n i=2 ∧ m j=2 := by have := pn i;have := pm j;omega
  have twoI := (original_threshold_prefix n hn 2 i).1 pair.1.ge
  have twoJ := (original_threshold_prefix m hm 2 j).1 pair.2.ge
  have past : originalThresholdCount n 3 ≤ a.val := by
    by_contra! earlier
    have := (original_threshold_prefix n hn 3 a).2 earlier
    omega
  have nonempty := (original_threshold_prefix n hn 3 ⟨0,hs⟩).1 head.ge
  dsimp only [a] at past
  exact ⟨i,j,idx,pair.1,pair.2,by omega⟩

/-- In degree three the full side is the unique escaping color.
Outside the already paid top, a genuine binary mixed column must beat
the pure 3-axis strictly, in either orientation. -/
theorem strict_cubic_escape_must_have_binary_overrun (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (three : diagonal F.n F.m (F.r+2)-1=3) :
    let μ := matchingEdges (F.G.induce K.core)
    (F.n ⟨0,F.hs⟩=3 ∧ F.t≤μ ∧ μ<F.s ∧ originalThresholdCount F.n 3+F.t<
      originalThresholdCount F.n 2+originalThresholdCount F.m 2) ∨
    (F.m ⟨0,F.ht⟩=3 ∧ F.s≤μ ∧ μ<F.t ∧ originalThresholdCount F.m 3+F.s<
      originalThresholdCount F.m 2+originalThresholdCount F.n 2) := by
  intro μ
  obtain ⟨_,z,zlt,gap,below⟩ := strict_mixed_columns_exceed_exposure F paid K
  have live : F.r+z<F.s+F.t-1 := by dsimp [StrictFamily.rank,rowCount] at zlt;omega
  have top : diagonal F.n F.m (F.r+2)=4 := by omega
  rw [top] at below
  have single := strict_full_head_unique_escape F paid K
  have escape := strict_source_one_list_escapes F paid K
  change μ+(F.rank-matchingEdges F.G)<max F.s F.t at escape
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  by_cases red : F.n ⟨0,F.hs⟩=3
  · obtain ⟨_,_,_,_,_,bound⟩ := cubic_mixed_corner_length F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm red live below gap
    have inner := (single.1 (red.trans three.symm)).1
    exact Or.inl ⟨red,inner,by change F.t≤μ at inner;omega,bound⟩
  · have up := nc ⟨0,F.hs⟩
    have blue : F.m ⟨0,F.ht⟩=3 := by
      have opp := mc ⟨0,F.ht⟩
      by_contra! notFull
      have hi := minimal_subcap_heads_force_degree_six F paid (by omega) (by omega)
      omega
    have swap : monochromeHeight F.m F.n (F.r+z)=monochromeHeight F.n F.m (F.r+z) := by
      unfold monochromeHeight;apply max_comm
    have eq := diagonal_swap F.m F.n (F.r+z+2)
    obtain ⟨_,_,_,_,_,bound⟩ := cubic_mixed_corner_length (r:=F.r) (z:=z) F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn blue
      (by omega) (by rw [eq];exact below) (by rw [eq,swap];exact gap)
    have inner := (single.2 (blue.trans three.symm)).1
    exact Or.inr ⟨blue,inner,by change F.s≤μ at inner;omega,bound⟩

#print axioms cubic_mixed_corner_length
#print axioms strict_cubic_escape_must_have_binary_overrun
end JSP452Audit.StarHost
