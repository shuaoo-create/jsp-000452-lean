import CubicStrictColumnWinners
namespace JSP452Audit.StarHost
universe u

private theorem head_of_threshold {s : ℕ} (hs : 0<s) (n : Fin s→ℕ) (hn : Antitone n) (k : ℕ)
    (pos : 0<originalThresholdCount n k) (cap : n ⟨0,hs⟩≤k) : n ⟨0,hs⟩=k :=
  le_antisymm cap ((original_threshold_prefix n hn k ⟨0,hs⟩).2 pos)

/-- The surviving cubic branch actually has a three-leaf head and the
exact single-side row area, in the corresponding original orientation. -/
theorem strict_cubic_full_head_axis (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (three : diagonal F.n F.m (F.r+2)-1=3)
    (both : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)) :
    let E := rowEnergy F.n F.m F.r
    let h := highestWidth F.n F.m F.r
    (F.n ⟨0,F.hs⟩=3 ∧ E=(∑i,F.n i)+3*(F.t-1-F.r)+h) ∨
      (F.m ⟨0,F.ht⟩=3 ∧ E=(∑j,F.m j)+3*(F.s-1-F.r)+h) := by
  intro E h
  have top : diagonal F.n F.m (F.r+2)=4 := by omega
  have area := cubic_original_height_profile F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm top
  change E=F.rank+widthAt F.n F.m F.r 2+widthAt F.n F.m F.r 3+h at area
  obtain ⟨nr,mr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  have count : F.rank+F.r+1=F.s+F.t := by
    change F.s+F.t-1-F.r+F.r+1=F.s+F.t;omega
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  rcases cubic_embedded_columns_same_side F paid K three both with ⟨_,p,w,v⟩|⟨_,q,w,v⟩
  · have value := cubic_original_leaf_sum F.n F.pn (fun i => (nc i).trans_eq three)
    exact Or.inl ⟨head_of_threshold F.hs F.n F.hn 3 p ((nc _).trans_eq three),by omega⟩
  · have value := cubic_original_leaf_sum F.m F.pm (fun j => (mc j).trans_eq three)
    exact Or.inr ⟨head_of_threshold F.ht F.m F.hm 3 q ((mc _).trans_eq three),by omega⟩

#print axioms strict_cubic_full_head_axis
end JSP452Audit.StarHost
