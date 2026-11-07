import InteriorHeightArea
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem interior_total_from_joint (D N nB nZ e₀ a μ ρ h ε β E EB EZ L LB LZ : ℕ)
    (pos : 0<D) (fit : e₀≤μ) (balance : nZ+e₀=N) (split : nB+a=nZ)
    (orig : E=N+L+h) (b : nB+LB≤EB) (z : nZ+LZ≤EZ)
    (joint : D*(a+2*μ)+D*ρ+ε+β+EB+EZ<2*E) :
    (D-1)*(a+2*μ)+LB+LZ+2*(μ-e₀)+D*ρ+ε+β<2*L+2*h := by
  have prod : D*(a+2*μ)=(D-1)*(a+2*μ)+(a+2*μ) := by
    conv_lhs => rw [show D=D-1+1 by omega,Nat.add_mul,Nat.one_mul]
  omega

def UnpaidHeight {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ) : Prop :=
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j

theorem actual_unpaid_height {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (top : diagonal n m (r+2)=D+1) (deg : 2≤D) (width : highestWidth n m r≤minimumExposure G D)
    (original : N=rowCount s t r) (esc : matchingEdges (G.induce K.core)<s)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r)) :
    ∃j,2≤j ∧ j≤D ∧ UnpaidHeight G K n m r j := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  let k := matchingEdges (G.induce K.rest)
  have joint := joint_rows_strict_area G K n m r N d _ cap data
  have ext := data.1
  obtain ⟨_,fit,_,base,_,_,_,_⟩ := ext
  change W.loss≤μ at fit
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  have area := original_area_by_height hs ht n m hn hm pn pm top (by omega)
  rw [←original] at area
  have b := interior_area_lower (r:=r+a) (D:=D) live ht (W.entries n) m (W.entries_positive n pn) pm (by omega)
  have z := interior_area_lower (r:=r) (D:=D) live ht J m (common_erased_positive n W a μ) pm (by omega)
  have sZ := data.2.2.1
  have whole := data.2.2.2.1
  have matchZ := whole_core_erasure_exact_rank G K
  change rowCount W.len t r=matchingEdges (eraseInternal G K.core)+d+(μ-W.loss) at sZ
  change rowCount W.len t r+W.loss=N at whole
  change rowCount W.len t (r+a)=k+d+(μ-W.loss) at base
  change matchingEdges (eraseInternal G K.core)=a+k at matchZ
  have split : rowCount W.len t (r+a)+a=rowCount W.len t r := by omega
  have total := interior_total_from_joint D N _ _ W.loss a μ (minimumExposure G D) (highestWidth n m r)
    (G.induce K.roots).edgeSet.ncard (crossCount G K.roots K.rest) _ _ _ _ _ _ (by omega) fit whole split area b z joint
  have buffer : 2*highestWidth n m r≤D*minimumExposure G D := by
    exact (Nat.mul_le_mul_left 2 width).trans (Nat.mul_le_mul_right _ deg)
  by_contra! absent
  have per (q:ℕ) (hq:q∈Finset.range (D-1)) :
      2*widthAt n m r (q+2) ≤ a+2*μ+widthAt (W.entries n) m (r+a) (q+2)+widthAt J m r (q+2) := by
    have limit := Finset.mem_range.mp hq
    exact Nat.le_of_not_gt (absent (q+2) (by omega) (by omega))
  have sums := Finset.sum_le_sum (s:=Finset.range (D-1)) per
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sums
  norm_cast at sums
  rw [show (D-1)*a+2*((D-1)*μ)=(D-1)*(a+2*μ) by ring] at sums
  change 2*interiorArea n m r D ≤ (D-1)*(a+2*μ)+interiorArea (W.entries n) m (r+a) D+interiorArea J m r D at sums
  omega

#print axioms interior_total_from_joint
#print axioms actual_unpaid_height
end JSP452Audit.StarHost
