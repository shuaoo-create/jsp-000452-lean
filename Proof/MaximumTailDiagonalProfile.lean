import MaximumPrefixPairInTails
namespace JSP452Audit.StarHost

/-- Cutting only redundant initial maximum heads preserves every
diagonal beyond the cut, including the diagonals after the finite row. -/
theorem maximum_tail_diagonal {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (i : Fin s) (j : Fin t) (cut : i.val+j.val=r) (red : ∀z,n z≤n i) (blue : ∀z,m z≤m j) (k : ℕ) :
    diagonal (originalTail n i) (originalTail m j) (k+2)=diagonal n m (r+k+2) := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨x,y⟩ member
    have idx := (Finset.mem_filter.mp member).2
    change x.val+1+(y.val+1)=k+2 at idx
    let u : Fin s := ⟨i.val+x.val,by have := i.isLt;have := x.isLt;omega⟩
    let v : Fin t := ⟨j.val+y.val,by have := j.isLt;have := y.isLt;omega⟩
    have eq : u.val+v.val+2=r+k+2 := by dsimp [u,v];omega
    have lower := antiDiag_member n m u v
    rw [eq] at lower
    change originalTail n i x+originalTail m j y-1≤_
    rw [tail_entry_original,tail_entry_original];exact lower
  · apply Finset.sup_le
    rintro ⟨u,v⟩ member
    have idx := (Finset.mem_filter.mp member).2
    change u.val+1+(v.val+1)=r+k+2 at idx
    obtain ⟨x,y,rx,by',sum,px,py⟩ := maximum_prefix_pair_in_tails n m hn hm i u j v red blue (by omega)
    let xx : Fin (s-i.val) := ⟨x.val-i.val,by change i.val≤x.val at rx;have := x.isLt;omega⟩
    let yy : Fin (t-j.val) := ⟨y.val-j.val,by change j.val≤y.val at by';have := y.isLt;omega⟩
    have backx : i.val+xx.val=x.val := by dsimp [xx];change i.val≤x.val at rx;omega
    have backy : j.val+yy.val=y.val := by dsimp [yy];change j.val≤y.val at by';omega
    have eq : xx.val+yy.val+2=k+2 := by omega
    have ex : originalTail n i xx=n x := by rw [tail_entry_original];congr 1;exact Fin.ext backx
    have ey : originalTail m j yy=m y := by rw [tail_entry_original];congr 1;exact Fin.ext backy
    have lower := antiDiag_member (originalTail n i) (originalTail m j) xx yy
    rw [eq,ex,ey] at lower
    change n u+m v-1≤_
    omega

theorem maximum_tail_rank {s t r : ℕ} (i : Fin s) (j : Fin t) (cut : i.val+j.val=r) :
    rowCount (s-i.val) (t-j.val) 0=rowCount s t r := by
  unfold rowCount;have := i.isLt;have := j.isLt;omega

theorem maximum_tail_full_profile {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (i : Fin s) (j : Fin t) (cut : i.val+j.val=r) (red : ∀z,n z≤n i) (blue : ∀z,m z≤m j) :
    (∀z,rowEnergy (originalTail n i) (originalTail m j) z=rowEnergy n m (r+z)) ∧
    highestWidth (originalTail n i) (originalTail m j) 0=highestWidth n m r := by
  have cols := maximum_tail_diagonal n m hn hm i j cut red blue
  have rank := maximum_tail_rank i j cut
  constructor
  · intro z
    have count : rowCount (s-i.val) (t-j.val) z=rowCount s t (r+z) := by
      unfold rowCount;have := i.isLt;have := j.isLt;omega
    unfold rowEnergy;rw [count]
    exact Finset.sum_congr rfl (fun k _ => by simpa only [Nat.add_assoc] using cols (z+k))
  · unfold highestWidth highestOffsets
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_range,Nat.zero_add,rank]
    rw [cols z,show diagonal (originalTail n i) (originalTail m j) 2=diagonal n m (r+2) by simpa using cols 0]

#print axioms maximum_tail_diagonal
#print axioms maximum_tail_rank
#print axioms maximum_tail_full_profile
end JSP452Audit.StarHost