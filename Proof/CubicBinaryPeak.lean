import StrictDoubleEmbeddingFromFour
import CubicOriginalAxis
namespace JSP452Audit.StarHost

/-- At degree three a pure full-head axis cannot have a genuine 3/2
threshold rectangle in each orientation. Every count in the two width
bounds is positive. The skipped count r starts at zero. -/
theorem two_cubic_heads_pay_axis (s t r E e M a k B ζ β ρ h d A P b q : ℕ)
    (before : r<t) (rank : M+k+d+r+1=s+t) (guard : k+a+2*d+r≤s)
    (width : h≤ρ) (deficit : ρ+1≤d) (redRect : P+b-1-r≤h) (blueRect : A+q-1-r≤h)
    (bpos : 1≤b) (qpos : 1≤q)
    (axis : E≤s+A+P+3*(t-1-r)+h)
    (edge : 2*e+ζ=6*M+3*ρ+β+2*B) (rk : k≤B) (root : 3*ρ+ζ≤2*h+2) : E≤e := by
  have x : P+b≤h+r+1 := by omega
  have y : A+q≤h+r+1 := by omega
  have rem : t-1-r+r+1=t := by omega
  linarith only [rank,guard,width,deficit,x,y,bpos,qpos,axis,edge,rk,root,rem,Nat.zero_le a,Nat.zero_le β]

/-- Once the opposite head is binary, only the genuine 3/2 rectangle can
attain the height four. This determines its exact untruncated width. -/
theorem cubic_binary_peak_width {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (ncap : n ⟨0,hs⟩≤3) (mcap : m ⟨0,ht⟩≤2)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=4) :
    0<originalThresholdCount n 3 ∧ 0<originalThresholdCount m 2 ∧
      originalThresholdCount n 3+originalThresholdCount m 2=highestWidth n m r+r+1 := by
  have present : 0<widthAt n m r 4 := Finset.card_pos.mpr ⟨0,Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr live,by simp [top]⟩⟩
  obtain ⟨a,b,ap,bp,high,x,y,w⟩ := original_column_real_winner hs ht n m hn hm pn pm (by decide : 0<4) present
  have naa : a≤n ⟨0,hs⟩ := (original_threshold_prefix n hn a ⟨0,hs⟩).2 x
  have mbb : b≤m ⟨0,ht⟩ := (original_threshold_prefix m hm b ⟨0,ht⟩).2 y
  have red : a=3 := by omega
  have blue : b=2 := by omega
  subst a;subst b
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at peak
  exact ⟨x,y,by omega⟩

#print axioms two_cubic_heads_pay_axis
#print axioms cubic_binary_peak_width
end JSP452Audit.StarHost
