import HighestColumn

namespace JSP452Audit.StarHost

/-- Horizontal width of the remaining original profile at a given height. -/
def offsetsAt {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r h : ℕ) : Finset ℕ :=
  (Finset.range (rowCount s t r)).filter fun d => h ≤ diagonal n m (r+d+2)

def widthAt {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r h : ℕ) : ℕ :=
  (offsetsAt n m r h).card

/-- Number of entries of the original suffix large enough to pay height a. -/
def tailWidthAt {s : ℕ} (n : Fin s → ℕ) (i : Fin s) (a : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (s-i.val))).filter fun k => a ≤ originalTail n i k).card

/-- All suffix offsets from i through x are distinct and meet any threshold
which the last index x still meets. -/
theorem span_le_tailWidthAt {s : ℕ} (n : Fin s → ℕ) (hn : Antitone n)
    (i x : Fin s) (ix : i ≤ x) (a : ℕ) (fits : a ≤ n x) :
    x.val+1-i.val ≤ tailWidthAt n i a := by
  let F := ((Finset.univ : Finset (Fin (s-i.val))).filter fun k => a ≤ originalTail n i k)
  let offset (k : Fin (x.val+1-i.val)) : Fin (s-i.val) :=
    ⟨k.val,by have := k.isLt; have := x.isLt; omega⟩
  have mem (k : Fin (x.val+1-i.val)) : offset k ∈ F := by
    let z : Fin s := ⟨i.val+k.val,by have := k.isLt; have := x.isLt; omega⟩
    have zx : z ≤ x := by change i.val+k.val ≤ x.val; have := k.isLt; omega
    have tail : originalTail n i (offset k) = n z := dif_pos z.isLt
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,tail ▸ fits.trans (hn zx)⟩
  let code (k : Fin (x.val+1-i.val)) : ↥F := ⟨offset k,mem k⟩
  have inj : Function.Injective code := fun _ _ eq => Fin.ext (congrArg (fun z : ↥F => z.val.val) eq)
  change _ ≤ F.card
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_injective code inj

/-- At every positive height of positive width there is a legal suffix pair
and a positive integer split whose two actual threshold counts cover that width. -/
theorem height_column_pair {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j) (r h : ℕ)
    (pos : 0<h) (present : 0 < widthAt n m r h) :
    ∃ (i : Fin s) (j : Fin t) (a b : ℕ), i.val+j.val = r ∧ 0<a ∧ 0<b ∧
      a+b-1 = h ∧ 0 < tailWidthAt n i a ∧ 0 < tailWidthAt m j b ∧
      widthAt n m r h ≤ tailWidthAt n i a + tailWidthAt m j b - 1 := by
  let F := offsetsAt n m r h
  have hF : F.Nonempty := Finset.card_pos.mp present
  let d := F.max' hF
  have hd : d ∈ F := F.max'_mem hF
  have inside : d < rowCount s t r := Finset.mem_range.mp (Finset.mem_filter.mp hd).1
  have high : h ≤ diagonal n m (r+d+2) := (Finset.mem_filter.mp hd).2
  have width : widthAt n m r h ≤ d+1 := by
    have sub : F ⊆ Finset.range (d+1) := fun k hk => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (F.le_max' k hk))
    simpa [F,widthAt] using Finset.card_le_card sub
  obtain ⟨x,y,later,atMax⟩ := diagonal_attained n m hs ht (r+d) (by dsimp [rowCount] at inside; omega)
  let i : Fin s := ⟨min r x.val,by have := x.isLt; omega⟩
  let j : Fin t := ⟨r-i.val,by dsimp [i]; have := y.isLt; omega⟩
  have row : i.val+j.val=r := by dsimp [i,j]; omega
  have ix : i ≤ x := Nat.min_le_right _ _
  have jy : j ≤ y := by change r-min r x.val ≤ y.val; omega
  let a := min (n x) h
  let b := h+1-a
  have ax : a ≤ n x := Nat.min_le_left _ _
  have by' : b ≤ m y := by
    have py := pm y
    dsimp [a,b]; omega
  have ap : 0 < a := lt_min (pn x) pos
  have bp : 0 < b := by dsimp [b,a]; omega
  have split : a+b-1=h := by dsimp [b,a]; omega
  have ur := span_le_tailWidthAt n hn i x ix a ax
  have ub := span_le_tailWidthAt m hm j y jy b by'
  have le₁ : i.val ≤ x.val := ix
  have le₂ : j.val ≤ y.val := jy
  exact ⟨i,j,a,b,row,ap,bp,split,by omega,by omega,by omega⟩

#print axioms span_le_tailWidthAt
#print axioms height_column_pair
end JSP452Audit.StarHost
