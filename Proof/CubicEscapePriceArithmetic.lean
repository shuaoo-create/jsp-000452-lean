import CubicExteriorLayerCounts
namespace JSP452Audit.StarHost

/-- On a genuine strict mixed overrun, the 2-by-2 rectangle wins layer
three; the opposite side has no three-leaf star. -/
theorem cubic_overrun_profile {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=4)
    (mcap : m ⟨0,ht⟩≤2)
    (over : originalThresholdCount n 3+t<originalThresholdCount n 2+originalThresholdCount m 2) :
    let A := originalThresholdCount n 2
    let B := originalThresholdCount m 2
    (widthAt n m r 2=A+t-1-r ∨ widthAt n m r 2=s+B-1-r) ∧
      rowEnergy n m r≤rowCount s t r+widthAt n m r 2+(A+B-1-r)+highestWidth n m r := by
  intro A B
  have area := cubic_original_height_profile hs ht n m hn hm pn pm top
  obtain ⟨wh,vh⟩ := cubic_original_column_winners hs ht n m hn hm pn pm live top
  have w : widthAt n m r 2=A+t-1-r ∨ widthAt n m r 2=s+B-1-r :=
    wh.imp (fun h => h.2) (fun h => h.2)
  refine ⟨w,?_⟩
  change originalThresholdCount n 3+t<A+B at over
  rcases vh with ⟨_,v⟩|⟨_,_,v⟩|⟨q,_⟩
  · omega
  · change widthAt n m r 3=A+B-1-r at v;omega
  · have bad := (original_threshold_prefix m hm 3 ⟨0,ht⟩).2 q
    omega

/-- The genuine exterior has enough nonunit stars to lose at most one
root-plus-core block of width in each of the first three layers. -/
theorem cubic_binary_witness_pays (s t r N a μ S A B c h ρ ζ β E e eB w wB vB : ℕ)
    (length : s=S+μ) (rank : N=rowCount S t (r+a)+(a+μ))
    (one : 1≤h) (width : h≤ρ) (root : 3*ρ+ζ≤2*h+2)
    (edge : 2*e+ζ=6*(a+μ)+3*ρ+β+2*eB)
    (orig : E≤N+w+(A+B-1-r)+h) (winner : w=A+t-1-r ∨ w=s+B-1-r)
    (fit : A≤μ+c) (blue : S+B-1-(r+a)≤wB)
    (red : c+t-1-(r+a)≤wB) (mix : c+B-1-(r+a)≤vB)
    (out : rowCount S t (r+a)+wB+vB≤eB) : E≤e := by
  obtain left|right := winner <;> omega

/-- When the nonunit stars fit the core's order, the all-unit red
exterior already pays the strict mixed overrun. Both layer-two winners
are treated with the actual original edge account. -/
theorem cubic_small_nonunit_pays (s t r N a μ S A B P h ρ ζ β E e eB w : ℕ)
    (length : s=S+μ) (rank : N=rowCount S t (r+a)+(a+μ)) (tail : 3≤S)
    (one : 1≤h) (width : h≤ρ) (lim : ρ≤2) (root : 3*ρ+ζ≤2*h+2)
    (edge : 2*e+ζ=6*(a+μ)+3*ρ+β+2*eB)
    (orig : E≤N+w+(A+B-1-r)+h) (winner : w=A+t-1-r ∨ w=s+B-1-r)
    (fit : A≤μ) (size : 3*A+P≤2*μ+a+ρ)
    (peak : P+B=h+r+1) (present : 0<P) (over : P+t<A+B)
    (out : rowCount S t (r+a)+(S+B-1-(r+a))≤eB) : E≤e := by
  rcases winner with left|right <;> omega

#print axioms cubic_overrun_profile
#print axioms cubic_binary_witness_pays
#print axioms cubic_small_nonunit_pays
end JSP452Audit.StarHost
