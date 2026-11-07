import StrictBinaryUnitExteriorExcluded
namespace JSP452Audit.StarHost

/-- Reposition an actual old pair on its original diagonal so that it
belongs to both retained tails. Either moved entry remains within an
initial run of maximum heads, or moves earlier in its sorted list. -/
theorem maximum_prefix_pair_in_tails {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (i u : Fin s) (j v : Fin t) (red : ∀z,n z≤n i) (blue : ∀z,m z≤m j)
    (late : i.val+j.val≤u.val+v.val) :
    ∃x:Fin s,∃y:Fin t,i≤x ∧ j≤y ∧ x.val+y.val=u.val+v.val ∧ n u≤n x ∧ m v≤m y := by
  by_cases left : u< i
  · let y : Fin t := ⟨u.val+v.val-i.val,by
      change u.val< i.val at left;have := v.isLt;omega⟩
    have back : y≤v := by change u.val+v.val-i.val≤v.val;change u.val< i.val at left;omega
    exact ⟨i,y,le_rfl,by change j.val≤u.val+v.val-i.val;omega,by dsimp [y];omega,red _,hm back⟩
  by_cases right : v<j
  · let x : Fin s := ⟨u.val+v.val-j.val,by
      change v.val<j.val at right;have := u.isLt;omega⟩
    have back : x≤u := by change u.val+v.val-j.val≤u.val;change v.val<j.val at right;omega
    exact ⟨x,j,by change i.val≤u.val+v.val-j.val;omega,le_rfl,by dsimp [x];omega,hn back,blue _⟩
  exact ⟨u,v,le_of_not_gt left,le_of_not_gt right,rfl,le_rfl,le_rfl⟩

theorem tail_entry_original {s : ℕ} (n : Fin s→ℕ) (i : Fin s) (k : Fin (s-i.val)) :
    originalTail n i k=n ⟨i.val+k.val,by have := i.isLt;have := k.isLt;omega⟩ := dif_pos _

theorem tail_sorted_positive {s : ℕ} (n : Fin s→ℕ) (hn : Antitone n) (pn : ∀i,1≤n i) (i : Fin s) :
    Antitone (originalTail n i) ∧ ∀k,1≤originalTail n i k := by
  constructor
  · intro a b ab;rw [tail_entry_original,tail_entry_original];apply hn
    change i.val+a.val≤ i.val+b.val;exact Nat.add_le_add_left ab _
  · intro k;rw [tail_entry_original];exact pn _

#print axioms maximum_prefix_pair_in_tails
#print axioms tail_entry_original
#print axioms tail_sorted_positive
end JSP452Audit.StarHost