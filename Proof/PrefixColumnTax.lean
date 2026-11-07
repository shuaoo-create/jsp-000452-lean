import HeightColumnPair

namespace JSP452Audit.StarHost

/-- Move a maximizing pair on a later live antidiagonal back to any earlier
one; neither of its original positive-list entries decreases. -/
theorem earlier_diagonal_dominates {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    {i j : ℕ} (order : i ≤ j) (live : j < s+t-1) :
    diagonal n m (j+2) ≤ diagonal n m (i+2) := by
  obtain ⟨x,y,whereAt,maxAt⟩ := diagonal_attained n m hs ht j live
  let u : Fin s := ⟨min i x.val,by have := x.isLt; omega⟩
  let v : Fin t := ⟨i-u.val,by dsimp [u]; have := y.isLt; omega⟩
  have uv : u.val+v.val = i := by dsimp [u,v]; omega
  have ux : u ≤ x := Nat.min_le_right _ _
  have vy : v ≤ y := by change i - min i x.val ≤ y.val; omega
  have early := antiDiag_member n m u v
  rw [uv] at early
  have := hn ux
  have := hm vy
  omega

/-- Split at the actual prefix length, allowing a shift past the last column. -/
theorem rowEnergy_prefix_split {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r a : ℕ) :
    rowEnergy n m r =
      (∑ k ∈ Finset.range (min a (rowCount s t r)), diagonal n m (r+k+2)) + rowEnergy n m (r+a) := by
  by_cases inside : a ≤ rowCount s t r
  · rw [min_eq_left inside]
    have count : rowCount s t r = a+rowCount s t (r+a) := by dsimp [rowCount] at *; omega
    unfold rowEnergy
    conv_lhs => rw [count,Finset.sum_range_add]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => congrArg (diagonal n m) (by omega))
  · have after : rowCount s t (r+a) = 0 := by dsimp [rowCount] at *; omega
    simp [rowEnergy,min_eq_right (Nat.le_of_not_ge inside),after]

/-- The removed prefix pays at most D per position, with at most one extra
unit for each original column at the head height. -/
theorem prefix_column_tax {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (_pn : ∀ i, 1 ≤ n i) (_pm : ∀ j, 1 ≤ m j) (r a : ℕ) (_live : 0 < rowCount s t r) :
    rowEnergy n m r ≤ rowEnergy n m (r+a) + (diagonal n m (r+2)-1)*a + highestWidth n m r := by
  let p := min a (rowCount s t r)
  let D := diagonal n m (r+2)-1
  let peaks := highestOffsets n m r
  have charged (i : ℕ) (mem : i ∈ Finset.range p) :
      diagonal n m (r+i+2) ≤ D + if i∈peaks then 1 else 0 := by
    have bound := Finset.mem_range.mp mem
    have idx : i < rowCount s t r := Nat.lt_of_lt_of_le bound (Nat.min_le_right ..)
    have calm := earlier_diagonal_dominates hs ht n m hn hm (show r ≤ r+i by omega)
      (show r+i < s+t-1 by dsimp [rowCount] at idx; omega)
    by_cases eq : diagonal n m (r+i+2) = diagonal n m (r+2)
    · have hp : i∈peaks := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,eq⟩
      rw [if_pos hp]; dsimp [D]; omega
    · dsimp [D]; split_ifs <;> omega
  have tax := Finset.sum_le_sum charged
  rw [Finset.sum_add_distrib,Finset.sum_boole] at tax
  have count : ((Finset.range p).filter fun i => i ∈ peaks).card ≤ highestWidth n m r :=
    Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)
  change (∑ i ∈ Finset.range p, diagonal n m (r+i+2)) ≤ (∑ _i ∈ Finset.range p, D) + ((Finset.range p).filter fun i => i ∈ peaks).card at tax
  have regular : (∑ _i ∈ Finset.range p, D) ≤ D*a := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right D (Nat.min_le_left a (rowCount s t r))
  have split := rowEnergy_prefix_split n m r a
  change rowEnergy n m r ≤ rowEnergy n m (r+a) + D*a + _
  change rowEnergy n m r = (∑ i ∈ Finset.range p,diagonal n m (r+i+2)) + _ at split
  omega

/-- The achieved offsets at any fixed height form an initial segment. -/
theorem offsetsAt_eq_range {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m) (r h : ℕ) :
    offsetsAt n m r h = Finset.range (widthAt n m r h) := by
  let F := offsetsAt n m r h
  change F = Finset.range F.card
  by_cases present : F.Nonempty
  · let d := F.max' present
    have last : d ∈ F := F.max'_mem present
    have below : d < rowCount s t r := Finset.mem_range.mp (Finset.mem_filter.mp last).1
    have high : h ≤ diagonal n m (r+d+2) := (Finset.mem_filter.mp last).2
    have initial : F = Finset.range (d+1) := by
      ext j
      constructor
      · exact fun hj => Finset.mem_range.mpr (Nat.lt_succ_of_le (F.le_max' j hj))
      · intro hj
        have jd := Finset.mem_range.mp hj
        have dom := earlier_diagonal_dominates hs ht n m hn hm
          (show r+j ≤ r+d by omega) (show r+d<s+t-1 by dsimp [rowCount] at below; omega)
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),high.trans dom⟩
    rw [initial,Finset.card_range]
  · rw [Finset.not_nonempty_iff_eq_empty.mp present]; simp

/-- Shifting by a positions removes exactly the first min(a,width) qualifying
columns, including when the resulting row is empty. -/
theorem widthAt_shift {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m) (r a h : ℕ) :
    widthAt n m (r+a) h = widthAt n m r h - a := by
  have mem (j : ℕ) : j ∈ offsetsAt n m (r+a) h ↔ a+j ∈ offsetsAt n m r h := by
    simp only [offsetsAt,Finset.mem_filter,Finset.mem_range]
    rw [Nat.add_assoc r a j]
    exact and_congr_left (fun _ => by dsimp [rowCount]; omega)
  have cut (j : ℕ) : j < widthAt n m (r+a) h ↔ a+j < widthAt n m r h := by
    simpa only [offsetsAt_eq_range hs ht n m hn hm,Finset.mem_range] using mem j
  have l := cut (widthAt n m r h - a)
  have u := cut (widthAt n m (r+a) h)
  omega

#print axioms offsetsAt_eq_range
#print axioms widthAt_shift
#print axioms earlier_diagonal_dominates
#print axioms rowEnergy_prefix_split
#print axioms prefix_column_tax
end JSP452Audit.StarHost
