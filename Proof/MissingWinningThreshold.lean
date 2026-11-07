import CommonThresholdLoss
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def WinsHeight {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r j x y : ℕ) : Prop :=
  0<x ∧ 0<y ∧ x+y-1=j ∧ 0<originalThresholdCount n x ∧ 0<originalThresholdCount m y ∧
    widthAt n m r j=originalThresholdCount n x+originalThresholdCount m y-1-r

def MissingAtHeight {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ) : Prop :=
  let H := G.induce K.core
  let W := componentBudget H n
  let J := commonErasedDemand n W K.roots.ncard (matchingEdges H)
  ∀x y,WinsHeight n m r j x y → 2≤x ∧ originalThresholdCount J x=0 ∧
    originalThresholdCount n x≤matchingEdges H ∧ originalThresholdCount (W.entries n) x≤K.roots.ncard

/-- A rectangle still present at the two successors pays this height at
once. Therefore at an unpaid height every genuine winning rectangle has
a nonunit escaping-side threshold absent from the retained-root graph. -/
theorem unpaid_height_missing_threshold {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i)
    (esc : matchingEdges (G.induce K.core)<s) (loss : UnpaidHeight G K n m r j) :
    MissingAtHeight G K n m r j := by
  let H := G.induce K.core
  let μ := matchingEdges H
  let a := K.roots.ncard
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  have fit : W.loss≤μ := component_budget_loss_le H n
  have live : 0<W.len := by change μ<s at esc;dsimp only [RemovalBudget.len];omega
  change a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j at loss
  intro x y win
  obtain ⟨px,_,height,_,right,area⟩ := win
  obtain ⟨nL,nJ,LJ,JL⟩ := common_threshold_floors n hn pn W a μ x fit
  change originalThresholdCount n x≤μ+originalThresholdCount J x at nJ
  change originalThresholdCount (W.entries n) x≤a+originalThresholdCount J x at LJ
  change originalThresholdCount J x≤originalThresholdCount (W.entries n) x at JL
  have zero : originalThresholdCount J x=0 := by
    by_contra! present
    have posJ : 0<originalThresholdCount J x := by omega
    have posL : 0<originalThresholdCount (W.entries n) x := posJ.trans_le JL
    have b := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm height posL right
    have z := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a μ) hm height posJ right
    omega
  have units : originalThresholdCount J 1=W.len := original_threshold_one J (common_erased_positive n W a μ)
  have nonunit : 2≤x := by
    by_contra! low
    have eq : x=1 := by omega
    rw [eq,units] at zero;omega
  exact ⟨nonunit,zero,by change originalThresholdCount n x≤μ;omega,by change originalThresholdCount (W.entries n) x≤a;omega⟩

def MissingHeightWitness {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) : Prop :=
  ∃j,2≤j ∧ j≤D ∧ UnpaidHeight G K n m r j ∧ (∃x y,WinsHeight n m r j x y) ∧ MissingAtHeight G K n m r j

theorem actual_missing_height {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (top : diagonal n m (r+2)=D+1) (deg : 2≤D) (width : highestWidth n m r≤minimumExposure G D)
    (original : N=rowCount s t r) (esc : matchingEdges (G.induce K.core)<s)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r)) : MissingHeightWitness G K n m r := by
  obtain ⟨j,lo,hi,bad⟩ := actual_unpaid_height G K n m r N d hs ht hn hm pn pm top deg width original esc cap data
  have fee := bad
  unfold UnpaidHeight at fee
  have present : 0<widthAt n m r j := by omega
  obtain ⟨x,y,px,py,h,nx,my,rect⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j) present
  exact ⟨j,lo,hi,bad,⟨x,y,px,py,h,nx,my,rect⟩,unpaid_height_missing_threshold G K n m r j hn hm pn esc bad⟩

#print axioms unpaid_height_missing_threshold
#print axioms actual_missing_height
end JSP452Audit.StarHost
