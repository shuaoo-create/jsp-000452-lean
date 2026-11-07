import OriginalUnitAxisArea
namespace JSP452Audit.StarHost

/-- A blue head of at least two forces every intervening (0,j) corner
onto the top plateau when the first red head already equals D. -/
theorem opposite_tail_unit_after_width {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pm : ∀j,1≤m j)
    (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1)
    (j : Fin t) (late : r+highestWidth n m r≤j.val) : m j=1 := by
  classical
  by_contra no
  have large : 2≤m j := by have pos:=pm j;omega
  have sub : Finset.range (j.val+1-r)⊆highestOffsets n m r := by
    intro x hx
    have small := Finset.mem_range.mp hx
    have idx : r+x≤j.val := by omega
    have enough : r+x<s+t-1 := by have := j.isLt;omega
    let b : Fin t := ⟨r+x,idx.trans_lt j.isLt⟩
    have bound := antiDiag_member n m ⟨0,hs⟩ b
    change n ⟨0,hs⟩+m b-1≤diagonal n m (0+(r+x)+2) at bound
    rw [head,Nat.zero_add] at bound
    have nonunit := hm (show b≤j from idx)
    have ceil := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+x by omega) enough
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by dsimp [rowCount];omega),by omega⟩
  have width := Finset.card_le_card sub
  change (Finset.range (j.val+1-r)).card≤highestWidth n m r at width
  rw [Finset.card_range] at width
  omega

theorem embedded_head_axis_upper {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pm : ∀j,1≤m j)
    (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1)
    (room : s+r+highestWidth n m r≤t) :
    rowEnergy n m r≤(t-1-r)*D+(∑i,n i)+highestWidth n m r := by
  classical
  have live : r<t := by omega
  let L := rowCount s t r
  let S := highestOffsets n m r
  have point (x:ℕ) (hx:x∈Finset.range L) :
      diagonal n m (r+x+2)≤unitAxisValue n t D (r+x)+(if x∈S then 1 else 0) := by
    have small := Finset.mem_range.mp hx
    change x<rowCount s t r at small
    have avail : r+x<s+t-1 := by dsimp [rowCount] at small;omega
    have cap := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+x by omega) avail
    by_cases early : r+x<t-1
    · rw [unitAxisValue,if_pos early]
      by_cases peak : diagonal n m (r+x+2)=diagonal n m (r+2)
      · have mem : x∈S := Finset.mem_filter.mpr ⟨hx,peak⟩
        rw [if_pos mem];omega
      · have out : x∉S := fun h => peak (Finset.mem_filter.mp h).2
        rw [if_neg out];omega
    obtain ⟨i,j,whereAt,attain⟩ := diagonal_attained n m hs ht (r+x) avail
    have late : r+highestWidth n m r≤j.val := by have hi:=i.isLt;omega
    have one := opposite_tail_unit_after_width hs ht n m hn hm pm head top j late
    have index : r+x-(t-1)≤ i.val := by have hj:=j.isLt;omega
    let a : Fin s := ⟨r+x-(t-1),index.trans_lt i.isLt⟩
    have bound := hn (show a≤ i from index)
    have exactVal : unitAxisValue n t D (r+x)=n a := by
      rw [unitAxisValue,if_neg early];exact dif_pos a.isLt
    rw [exactVal,attain,one];omega
  have bound := Finset.sum_le_sum (s:=Finset.range L) point
  rw [Finset.sum_add_distrib,Finset.sum_boole] at bound
  have filter : (Finset.range L).filter (fun x => x∈S)=S := by
    ext x;exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,h⟩⟩
  rw [filter,unit_axis_row_sum n D live] at bound
  exact bound

#print axioms opposite_tail_unit_after_width
#print axioms embedded_head_axis_upper
end JSP452Audit.StarHost
