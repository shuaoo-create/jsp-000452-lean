import SumAllSuppressionLayers
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_upper_pure_only {s t r D b : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (head : m ⟨0,ht⟩=b) (top : diagonal n m (r+2)=D+1) (live : 0<rowCount s t r) (large : 2≤b)
    (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t) (j : ℕ) (lo : b+2≤j) (hi : j≤D) :
    widthAt n m r j≤originalThresholdCount n j+t-1-r := by
  have opts := full_opposite_three_options hs ht n m hn hm pn pm (by omega : 3≤j)
    (actual_height_positive n m live top j (by omega)) budget
  rcases opts with pure|⟨full,_⟩|⟨full,_⟩
  · exact pure
  · have bad := (original_threshold_prefix m hm j ⟨0,ht⟩).2 full;omega
  · have bad := (original_threshold_prefix m hm (j-1) ⟨0,ht⟩).2 full;omega

theorem full_boundary_pure_or_reserve {s t r D b : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (head : m ⟨0,ht⟩=b) (top : diagonal n m (r+2)=D+1)
    (live : 0<rowCount s t r) (large : 2≤b) (sub : b<D) (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t)
    (esc : matchingEdges (G.induce K.core)<s) (ρ : ℕ) (limit : originalThresholdCount m 2≤r+ρ)
    (px : 0<originalThresholdCount n 2) :
    widthAt n m r (b+1)≤originalThresholdCount n (b+1)+t-1-r ∨
      2*widthAt n m r (b+1)≤basicCapacity G K n m r (b+1)+2*ρ := by
  have opts := full_opposite_three_options hs ht n m hn hm pn pm (by omega : 3≤b+1)
    (actual_height_positive n m live top (b+1) (by omega)) budget
  let μ := matchingEdges (G.induce K.core)
  let Q := basicCapacity G K n m r (b+1)
  let C := widthAt n m r (b+1)
  have base : 2*μ≤Q := by dsimp [μ,Q,basicCapacity];omega
  rcases opts with pure|⟨full,_⟩|⟨gp,eq⟩
  · exact Or.inl pure
  · have bad := (original_threshold_prefix m hm (b+1) ⟨0,ht⟩).2 full;omega
  · right
    by_contra! big
    change Q+2*ρ<2*C at big
    have gap : UnpaidHeight G K n m r (b+1) := by change Q<2*C;omega
    have win : WinsHeight n m r (b+1) 2 b := by
      simp only [Nat.add_sub_cancel] at gp eq
      exact ⟨by omega,by omega,by omega,px,gp,eq⟩
    have few := (unpaid_height_missing_threshold G K n m r (b+1) hn hm pn esc gap 2 b win).2.2.1
    have mono := threshold_anti_height m large
    change originalThresholdCount n 2≤μ at few
    have w : C=originalThresholdCount n 2+originalThresholdCount m b-1-r := win.2.2.2.2.2
    omega

#print axioms full_upper_pure_only
#print axioms full_boundary_pure_or_reserve
end JSP452Audit.StarHost