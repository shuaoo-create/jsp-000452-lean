import CubicEmbeddedPriceThresholds
namespace JSP452Audit.StarHost
universe u

/-- At a cubic embedded strict source only one side can win the height-two
and height-three columns together. Both winning thresholds are inhabited. -/
theorem cubic_embedded_columns_same_side (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (three : diagonal F.n F.m (F.r+2)-1=3)
    (both : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)) :
    let A := originalThresholdCount F.n 2
    let B := originalThresholdCount F.m 2
    let P := originalThresholdCount F.n 3
    let Q := originalThresholdCount F.m 3
    let W := widthAt F.n F.m F.r 2
    let V := widthAt F.n F.m F.r 3
    (0<A ∧ 0<P ∧ W=A+F.t-1-F.r ∧ V=P+F.t-1-F.r) ∨
      (0<B ∧ 0<Q ∧ W=F.s+B-1-F.r ∧ V=F.s+Q-1-F.r) := by
  intro A B P Q W V
  let h := highestWidth F.n F.m F.r
  let E := rowEnergy F.n F.m F.r
  let e := F.G.edgeSet.ncard
  let u := ∑i,F.n i
  let v := ∑j,F.m j
  have top : diagonal F.n F.m (F.r+2)=4 := by omega
  have strict := F.strict
  change e<E at strict
  have bounds := cubic_embedded_price_thresholds F paid K three both
  change F.rank+u+v+h≤e+2*F.r+2 ∧ 2*F.rank+2*h≤e at bounds
  have area := cubic_original_height_profile F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm top
  change E=F.rank+W+V+h at area
  have wc := cubic_original_column_winners F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.live top
  change ((0<A ∧ W=A+F.t-1-F.r) ∨ (0<B ∧ W=F.s+B-1-F.r)) ∧
      ((0<P ∧ V=P+F.t-1-F.r) ∨ (0<A ∧ 0<B ∧ V=A+B-1-F.r) ∨ (0<Q ∧ V=F.s+Q-1-F.r)) at wc
  have high := width_at_actual_top (r:=F.r) F.hs F.ht F.n F.m F.hn F.hm
  rw [top] at high
  have wp : 0<W := Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr F.live,by simp [top]⟩⟩
  have vp : 0<V := Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr F.live,by simp [top]⟩⟩
  have count : F.rank+F.r+1=F.s+F.t := by
    have live:=F.live
    change 0<F.s+F.t-1-F.r at live
    change F.s+F.t-1-F.r+F.r+1=F.s+F.t;omega
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have fN := cubic_original_leaf_sum F.n F.pn (fun i => (nc i).trans_eq three)
  have fM := cubic_original_leaf_sum F.m F.pm (fun j => (mc j).trans_eq three)
  change u=F.s+A+P at fN
  change v=F.t+B+Q at fM
  have aSmall : A≤F.s := original_threshold_le_length _ _
  have bSmall : B≤F.t := original_threshold_le_length _ _
  have mix (eq : V=A+B-1-F.r) : False := by
    rcases wc.1 with ⟨_,w⟩|⟨_,w⟩ <;> omega
  rcases wc.2 with ⟨p,vr⟩|⟨_,_,mixed⟩|⟨q,vb⟩
  · rcases wc.1 with ⟨a,wr⟩|⟨b,wb⟩
    · exact Or.inl ⟨a,p,wr,vr⟩
    · have rect := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm (a:=3) (b:=2)
        (by decide : 3+2-1=4) p b
      rw [high] at rect;change P+B-1-F.r≤h at rect;omega
  · exact (mix mixed).elim
  · rcases wc.1 with ⟨a,wr⟩|⟨b,wb⟩
    · have rect := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm (a:=2) (b:=3)
        (by decide : 2+3-1=4) a q
      rw [high] at rect;change A+Q-1-F.r≤h at rect;omega
    · exact Or.inr ⟨b,q,wb,vb⟩

#print axioms cubic_embedded_columns_same_side
end JSP452Audit.StarHost
