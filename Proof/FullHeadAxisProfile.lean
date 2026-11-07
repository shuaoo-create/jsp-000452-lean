import PersistentFullHeadSource
namespace JSP452Audit.StarHost

/-- In the last t columns the maximizing pair is charged to distinct
original blue entries; the last s columns also use distinct red entries. -/
theorem original_full_head_profile {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (lengths : s≤t) (before : r<s) (degree : 3≤D)
    (head : n ⟨0,hs⟩≤D) (top : diagonal n m (r+2)=D+1) :
    rowEnergy n m r+t≤(t-1-r)*D+(∑i,n i)+(∑j,m j)+highestWidth n m r := by
  classical
  let L := rowCount s t r
  let S := highestOffsets n m r
  have point (x:ℕ) (hx:x∈Finset.range L) :
      diagonal n m (r+x+2)+1≤
      unitAxisValue n t D (r+x)+unitAxisValue m s 1 (r+x)+(if x∈S then 1 else 0) := by
    have bound := Finset.mem_range.mp hx
    change x<rowCount s t r at bound
    have avail : r+x<s+t-1 := by dsimp [rowCount] at bound;omega
    by_cases early : r+x<s-1
    · have earlyT : r+x<t-1 := by omega
      rw [unitAxisValue,if_pos earlyT,unitAxisValue,if_pos early]
      have cap := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+x by omega) avail
      by_cases peak : diagonal n m (r+x+2)=diagonal n m (r+2)
      · have mem : x∈S := Finset.mem_filter.mpr ⟨hx,peak⟩
        rw [if_pos mem];omega
      · have out : x∉S := fun h => peak (Finset.mem_filter.mp h).2
        rw [if_neg out];omega
    obtain ⟨i,j,idx,value⟩ := diagonal_attained n m hs ht (r+x) avail
    have bindex : r+x-(s-1)≤ j.val := by have hi:=i.isLt;omega
    let b : Fin t := ⟨r+x-(s-1),bindex.trans_lt j.isLt⟩
    have bval : unitAxisValue m s 1 (r+x)=m b := by rw [unitAxisValue,if_neg early];exact dif_pos b.isLt
    have mb := hm (show b≤ j from bindex)
    have red : n i≤unitAxisValue n t D (r+x) := by
      by_cases first : r+x<t-1
      · rw [unitAxisValue,if_pos first]
        exact (hn (show (⟨0,hs⟩ : Fin s)≤ i from Nat.zero_le _)).trans head
      have idxA : r+x-(t-1)≤ i.val := by have hj:=j.isLt;omega
      let a : Fin s := ⟨r+x-(t-1),idxA.trans_lt i.isLt⟩
      rw [unitAxisValue,if_neg first,show padDemand n (r+x-(t-1))=n a from dif_pos a.isLt]
      exact hn (show a≤ i from idxA)
    rw [value,bval]
    have pos := pn i
    omega
  have sum := Finset.sum_le_sum (s:=Finset.range L) point
  simp only [Finset.sum_add_distrib] at sum
  rw [unit_axis_row_sum n D (before.trans_le lengths)] at sum
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] at sum
  have axisM : (∑x∈Finset.range L,unitAxisValue m s 1 (r+x))=(s-1-r)*1+∑j,m j := by
    change (∑x∈Finset.range (rowCount s t r),_)=_
    rw [show rowCount s t r=rowCount t s r by simp [rowCount,Nat.add_comm s t]]
    exact unit_axis_row_sum m 1 before
  rw [axisM,Finset.sum_boole] at sum
  have filter : (Finset.range L).filter (fun x => x∈S)=S := by
    ext x;exact ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).1,h⟩⟩
  rw [filter,mul_one] at sum
  change rowEnergy n m r+L≤(t-1-r)*D+(∑i,n i)+(s-1-r+(∑j,m j))+highestWidth n m r at sum
  have count : L=s-1-r+t := by dsimp [L,rowCount];omega
  omega

#print axioms original_full_head_profile
end JSP452Audit.StarHost
