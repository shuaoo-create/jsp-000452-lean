import CapacitySplit
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace JSP452Audit.StarHost

/-- Keep all but p+1 pieces of largest z, with explicit witnesses for both
ordering and the maximum among the retained pieces. Ties need no tie-break. -/
theorem heavy_piece_selection {I : Type*} [Fintype I] [DecidableEq I] (z : I → ℕ)
    (w : I → ℤ) (p : ℕ) (_pos : ∀ x, 0 < w x) (cap : ∀ x, w x ≤ p)
    (heavy : (p : ℤ)*(p+1) < ∑ i, w i) :
    ∃ T : Finset I, T.Nonempty ∧ Tᶜ.card = p+1 ∧
      (∀ y ∈ Tᶜ, ∀ x ∈ T, z x ≤ z y) ∧
      (∑ i, w i) - (p : ℤ)*(p+1) ≤ (∑ x ∈ T, w x) ∧
      ∃ Z ∈ T, ∀ x ∈ T, z x ≤ z Z := by
  classical
  have count : p+1 < Fintype.card I := by
    by_contra! few
    have upper := Finset.sum_le_sum (s := Finset.univ) (fun x _ => cap x)
    have mulLe : p * Fintype.card I ≤ p * (p+1) := Nat.mul_le_mul_left p few
    have cast : (p : ℤ) * (Fintype.card I : ℤ) ≤ p * (p+1) := by exact_mod_cast mulLe
    have sumLe : (∑ i, w i) ≤ (p : ℤ) * (Fintype.card I : ℤ) := by
      simpa [mul_comm] using upper
    omega
  let menus := (Finset.univ : Finset (Finset I)).filter fun B => B.card=p+1
  let score (B : Finset I) := ∑ x ∈ B, z x
  have legal (B : Finset I) : B ∈ menus ↔ B.card=p+1 := by simp [menus]
  obtain ⟨B₀,_,size₀⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I))
    (n := p+1) (by simpa using count.le)
  obtain ⟨B,chosen,best⟩ := Finset.exists_max_image menus score ⟨B₀,(legal _).mpr size₀⟩
  have size := (legal B).mp chosen
  have left : Bᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,size]; omega
  obtain ⟨Z,hZ,peak⟩ := Finset.exists_max_image Bᶜ z left
  refine ⟨Bᶜ,left,by simpa using size,?_,?_,⟨Z,hZ,peak⟩⟩
  · intro y hy x hx
    have inside : y ∈ B := by simpa using hy
    have outside : x ∉ B := Finset.mem_compl.mp hx
    have fresh : x ∉ B.erase y := fun h => outside (Finset.mem_of_mem_erase h)
    have newSize : (insert x (B.erase y)).card = p+1 := by
      rw [Finset.card_insert_of_notMem fresh,Finset.card_erase_of_mem inside,size]
      omega
    have noGain := best (insert x (B.erase y)) ((legal _).mpr newSize)
    change (∑ i ∈ insert x (B.erase y), z i) ≤ ∑ i ∈ B, z i at noGain
    rw [Finset.sum_insert fresh] at noGain
    have old := Finset.sum_erase_add B z inside
    omega
  · have removed := Finset.sum_le_sum (s := B) (fun x _ => cap x)
    have bound : (∑ x ∈ B, w x) ≤ (p : ℤ)*(p+1) := by simpa [size,mul_comm] using removed
    have exactSum := Finset.sum_add_sum_compl B w
    omega

#print axioms heavy_piece_selection
end JSP452Audit.StarHost
