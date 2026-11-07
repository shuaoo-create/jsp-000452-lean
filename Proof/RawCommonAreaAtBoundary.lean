import OnePatternForAllNonunits
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def basicCapacity {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ) : ℕ :=
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let W := componentBudget (G.induce K.core) n
  a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt (commonErasedDemand n W a μ) m r j

theorem basic_capacity_total {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) :
    let a := K.roots.ncard
    let μ := matchingEdges (G.induce K.core)
    let W := componentBudget (G.induce K.core) n
    let J := commonErasedDemand n W a μ
    (∑z∈Finset.range (D-1),basicCapacity G K n m r (z+2))=
      (D-1)*(a+2*μ)+interiorArea (W.entries n) m (r+a) D+interiorArea J m r D := by
  intro a μ W J
  let M := a+2*μ
  change (∑z∈Finset.range (D-1),(M+widthAt (W.entries n) m (r+a) (z+2)+widthAt J m r (z+2)))=_
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [interiorArea,M]

theorem raw_strict_joint_total {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (pos : 0<D) (top : diagonal n m (r+2)=D+1) (nr : N=rowCount s t r) (esc : matchingEdges (G.induce K.core)<s)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (data : BothActualSuccessors G K n m r N d (rowEnergy n m r)) :
    let μ := matchingEdges (G.induce K.core)
    let W := componentBudget (G.induce K.core) n
    (∑z∈Finset.range (D-1),basicCapacity G K n m r (z+2))+D*minimumExposure G D+2*(μ-W.loss)<
      2*interiorArea n m r D+2*highestWidth n m r := by
  intro μ W
  let a := K.roots.ncard
  let J := commonErasedDemand n W a μ
  let k := matchingEdges (G.induce K.rest)
  have joint := joint_rows_strict_area G K n m r N d _ cap data
  have ext := data.1
  obtain ⟨_,fit,_,base,_,_,_,_⟩ := ext
  change W.loss≤μ at fit
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  have area := original_area_by_height hs ht n m hn hm pn pm top pos
  rw [←nr] at area
  have b := interior_area_lower (r:=r+a) (D:=D) live ht (W.entries n) m (W.entries_positive n pn) pm pos
  have z := interior_area_lower (r:=r) (D:=D) live ht J m (common_erased_positive n W a μ) pm pos
  have sZ := data.2.2.1
  have whole := data.2.2.2.1
  have matchZ := whole_core_erasure_exact_rank G K
  change rowCount W.len t r=matchingEdges (eraseInternal G K.core)+d+(μ-W.loss) at sZ
  change rowCount W.len t r+W.loss=N at whole
  change rowCount W.len t (r+a)=k+d+(μ-W.loss) at base
  change matchingEdges (eraseInternal G K.core)=a+k at matchZ
  have total := interior_total_from_joint D N _ _ W.loss a μ (minimumExposure G D) (highestWidth n m r)
    (G.induce K.roots).edgeSet.ncard (crossCount G K.roots K.rest) _ _ _ _ _ _ pos fit whole (by omega) area b z joint
  rw [basic_capacity_total]
  change (D-1)*(a+2*μ)+interiorArea (W.entries n) m (r+a) D+interiorArea J m r D+
    D*minimumExposure G D+2*(μ-W.loss)<2*interiorArea n m r D+2*highestWidth n m r
  omega

/-- At an internal blue prefix, both basic row widths bound the loss
of a two-head winner. If v2 is positive the exterior additionally has
the red 2 by blue y rectangle, on that same graph. -/
theorem raw_two_head_fee {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r j y : ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i)
    (esc : matchingEdges (G.induce K.core)<s)
    (active : 0<originalThresholdCount m j) (win : WinsHeight n m r j 2 y) (present : 0<widthAt n m r j)
    (few : originalThresholdCount n 2≤matchingEdges (G.induce K.core)) :
    let μ := matchingEdges (G.induce K.core)
    let W := componentBudget (G.induce K.core) n
    let δ := μ-W.loss
    let u := s-originalThresholdCount n 2
    let V := μ-originalThresholdCount n 2
    let v := originalThresholdCount (W.entries n) 2
    let C := basicCapacity G K n m r j
    2*widthAt n m r j+2*(u+δ+originalThresholdCount m j)≤C+2*originalThresholdCount m y ∧
      (0<v → 2*widthAt n m r j+(V+v)+u+δ+originalThresholdCount m j≤C+originalThresholdCount m y) := by
  intro μ W δ u V v C
  let a := K.roots.ncard
  let J := commonErasedDemand n W a μ
  have fit : W.loss≤μ := component_budget_loss_le _ _
  change μ<s at esc
  change originalThresholdCount n 2≤μ at few
  have live : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have BL := original_threshold_one (W.entries n) (W.entries_positive n pn)
  have ZL := original_threshold_one J (common_erased_positive n W a μ)
  have br := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
    (a:=1) (b:=j) (h:=j) (by omega) (BL.symm ▸ live) active
  have zr := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a μ) hm
    (a:=1) (b:=j) (h:=j) (by omega) (ZL.symm ▸ live) active
  rw [BL] at br;rw [ZL] at zr
  have len : W.len+μ=s+δ := by change (s-W.loss)+μ=s+(μ-W.loss);omega
  have f := original_threshold_le_length n 2
  have eq := win.2.2.2.2.2
  have cost : C=a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j := rfl
  dsimp only [u,V]
  constructor
  · omega
  · intro yes
    have b2 := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm win.2.2.1 yes win.2.2.2.2.1
    change v+originalThresholdCount m y-1-(r+a)≤widthAt (W.entries n) m (r+a) j at b2
    omega

#print axioms raw_strict_joint_total
#print axioms raw_two_head_fee
end JSP452Audit.StarHost
