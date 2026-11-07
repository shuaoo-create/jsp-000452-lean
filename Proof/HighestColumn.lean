import RowEnergy
import ExposureThreshold

namespace JSP452Audit.StarHost

/-- Positions in the remaining antidiagonal list that equal the current head. -/
def highestOffsets {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r : ℕ) : Finset ℕ :=
  (Finset.range (rowCount s t r)).filter fun d => diagonal n m (r+d+2) = diagonal n m (r+2)

def highestWidth {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r : ℕ) : ℕ :=
  (highestOffsets n m r).card

/-- Count the occurrences of the head of the suffix starting at i, including i. -/
def suffixHeadCount {s : ℕ} (n : Fin s → ℕ) (i : Fin s) : ℕ :=
  ((Finset.univ : Finset (Fin s)).filter fun z => i ≤ z ∧ n z = n i).card

/-- In a nonincreasing list a repeated endpoint gives a whole intervening
run. The embedding below explicitly enumerates its entries. -/
theorem span_le_suffixHeadCount {s : ℕ} (n : Fin s → ℕ) (hn : Antitone n)
    (i x : Fin s) (le : i ≤ x) (same : n i = n x) :
    x.val + 1 - i.val ≤ suffixHeadCount n i := by
  let F := ((Finset.univ : Finset (Fin s)).filter fun z => i ≤ z ∧ n z = n i)
  let entry (a : Fin (x.val + 1 - i.val)) : Fin s := ⟨i.val+a.val,by
    have h1 := a.isLt
    have h2 := x.isLt
    omega⟩
  have mem (a : Fin (x.val + 1 - i.val)) : entry a ∈ F := by
    have h1 : i ≤ entry a := by change i.val ≤ i.val+a.val; omega
    have h2 : entry a ≤ x := by change i.val+a.val ≤ x.val; have := a.isLt; omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1,le_antisymm (hn h1) (same ▸ hn h2)⟩
  let code (a : Fin (x.val + 1 - i.val)) : ↥F := ⟨entry a,mem a⟩
  have inj : Function.Injective code := by
    intro a b eq
    have e := congrArg (fun z : ↥F => z.val.val) eq
    change i.val+a.val = i.val+b.val at e
    exact Fin.ext (by omega)
  change x.val + 1 - i.val ≤ F.card
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective code inj

/-- The farthest offset of unchanged height yields an attaining pair on
the present row whose two equal-size suffix runs pay for the whole width. -/
theorem highest_column_pair {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j) (r : ℕ) (live : 0 < rowCount s t r) :
    ∃ (i : Fin s) (j : Fin t), i.val+j.val = r ∧
      diagonal n m (r+2) = n i + m j - 1 ∧
      highestWidth n m r ≤ suffixHeadCount n i + suffixHeadCount m j - 1 := by
  let F := highestOffsets n m r
  have first : 0 ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by simp⟩
  let hF : F.Nonempty := ⟨0,first⟩
  let d := F.max' hF
  have hd : d ∈ F := F.max'_mem hF
  have within : d < rowCount s t r := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  have tie : diagonal n m (r+d+2) = diagonal n m (r+2) := (Finset.mem_filter.mp hd).2
  have width : highestWidth n m r ≤ d+1 := by
    have sub : F ⊆ Finset.range (d+1) := fun k hk => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (F.le_max' k hk))
    simpa [F,highestWidth] using Finset.card_le_card sub
  obtain ⟨x,y,later,hxy⟩ := diagonal_attained n m hs ht (r+d) (by dsimp [rowCount] at within; omega)
  let i : Fin s := ⟨min r x.val,by have := x.isLt; omega⟩
  let j : Fin t := ⟨r-i.val,by dsimp [i]; have := y.isLt; omega⟩
  have row : i.val+j.val=r := by dsimp [i,j]; omega
  have ix : i ≤ x := Nat.min_le_right _ _
  have jy : j ≤ y := by change r-min r x.val ≤ y.val; omega
  have now := antiDiag_member n m i j
  rw [row] at now
  have nx := hn ix
  have my := hm jy
  have xp := pn x
  have yp := pm y
  have eqN : n i = n x := by omega
  have eqM : m j = m y := by omega
  have attains : diagonal n m (r+2) = n i + m j - 1 := by omega
  have red := span_le_suffixHeadCount n hn i x ix eqN
  have blue := span_le_suffixHeadCount m hm j y jy eqM
  exact ⟨i,j,row,attains,by omega⟩

/-- Reindex the head of the padded-demand suffix back into the original list. -/
theorem headWidth_eq_suffixHeadCount {s : ℕ} (n : Fin s → ℕ) (hn : Antitone n) (i : Fin s) :
    headWidth n i = suffixHeadCount n i := by
  let pos (k : Fin (s-i.val)) : Fin s := ⟨i.val+k.val,by have := k.isLt; have := i.isLt; omega⟩
  have tail (k : Fin (s-i.val)) : originalTail n i k = n (pos k) :=
    dif_pos (pos k).isLt
  have after (k : Fin (s-i.val)) : i ≤ pos k := by change i.val ≤ i.val+k.val; omega
  unfold headWidth suffixHeadCount
  apply Finset.card_bij (fun k _ => pos k)
  · intro k hk
    have att := (Finset.mem_filter.mp hk).2
    rw [tail] at att
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,after k,le_antisymm (hn (after k)) att⟩
  · intro k _ l _ eq
    have same := congrArg Fin.val eq
    change i.val+k.val = i.val+l.val at same
    exact Fin.ext (by omega)
  · intro x hx
    obtain ⟨_,after,eq⟩ := Finset.mem_filter.mp hx
    let k : Fin (s-i.val) := ⟨x.val-i.val,by have := x.isLt; have := i.isLt; omega⟩
    have back : pos k = x := Fin.ext (by dsimp [pos,k]; change i.val ≤ x.val at after; omega)
    refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,back⟩
    rw [tail,back,eq]

theorem highest_column_head_pair {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j) (r : ℕ) (live : 0 < rowCount s t r) :
    ∃ (i : Fin s) (j : Fin t), i.val+j.val = r ∧
      diagonal n m (r+2) = n i + m j - 1 ∧
      highestWidth n m r ≤ headWidth n i + headWidth m j - 1 := by
  obtain ⟨i,j,row,peak,width⟩ := highest_column_pair hs ht n m hn hm pn pm r live
  exact ⟨i,j,row,peak,by simpa only [headWidth_eq_suffixHeadCount n hn,headWidth_eq_suffixHeadCount m hm] using width⟩

#print axioms highest_column_head_pair
#print axioms span_le_suffixHeadCount
#print axioms highest_column_pair
end JSP452Audit.StarHost
