import StrictFullHeadGapAtLeastTwo
namespace JSP452Audit.StarHost

theorem fold_any_three_heights (D b h ρ δ : ℕ) (W C : ℕ→ℕ) (lo : 3≤b) (hi : b<D)
    (three : 2*W 2+2*W 3+2*W (b+1)+2*h≤C 2+C 3+C (b+1)+D*ρ+2*δ)
    (paid : ∀j,4≤j → j≤D → j≠b+1 → 2*W j≤C j) :
    2*(∑z∈Finset.range (D-1),W (z+2))+2*h≤(∑z∈Finset.range (D-1),C (z+2))+D*ρ+2*δ := by
  classical
  let I := Finset.range (D-1)
  let v := b-1
  let R := ((I.erase 0).erase 1).erase v
  have p0 : 0∈I := Finset.mem_range.mpr (by omega)
  have p1 : 1∈I.erase 0 := Finset.mem_erase.mpr ⟨by decide,Finset.mem_range.mpr (by omega)⟩
  have pv : v∈(I.erase 0).erase 1 := by
    dsimp [v];exact Finset.mem_erase.mpr ⟨by omega,Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩⟩
  have split (f:ℕ→ℕ) : (∑z∈I,f (z+2))=(∑z∈R,f (z+2))+f (b+1)+f 3+f 2 := by
    rw [←Finset.sum_erase_add _ (fun z => f (z+2)) p0,←Finset.sum_erase_add _ (fun z => f (z+2)) p1,
      ←Finset.sum_erase_add _ (fun z => f (z+2)) pv]
    change (∑z∈R,f (z+2))+f (v+2)+f 3+f 2=_
    rw [show v+2=b+1 by dsimp [v];omega]
  have price := Finset.sum_le_sum (s:=R) (fun z hz => show 2*W (z+2)≤C (z+2) by
    change z∈((I.erase 0).erase 1).erase v at hz
    obtain ⟨nv,hz⟩ := Finset.mem_erase.mp hz
    obtain ⟨n1,hz⟩ := Finset.mem_erase.mp hz
    obtain ⟨n0,hz⟩ := Finset.mem_erase.mp hz
    have bound := Finset.mem_range.mp hz
    dsimp [v] at nv;exact paid _ (by omega) (by omega) (by omega))
  rw [←Finset.mul_sum] at price
  change 2*(∑z∈I,W (z+2))+2*h≤(∑z∈I,C (z+2))+D*ρ+2*δ
  rw [split W,split C];omega

#print axioms fold_any_three_heights
end JSP452Audit.StarHost