import RankSplitDef
import BinaryRowProfile
import PackingFloor
import ColumnDeletion
import BaseDeletionReserve
namespace JSP452Audit.StarHost
open SimpleGraph
theorem rank_floor_of_splittable {X : Type*} [Finite X] {s t : ℕ}
    (G : SimpleGraph X) (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (force : Forces G (forest n) (forest m))
    (split : CanSplitRank G) : s+t-2 ≤ matchingEdges G := by
  by_contra! low
  let u := min (s-1) (matchingEdges G)
  obtain ⟨R,sub,rc,bc⟩ := split u (Nat.min_le_right _ _)
  rcases force R sub with red | blue
  · have floor := forest_copy_matching R n pn red
    rw [Fintype.card_fin] at floor
    dsimp [u] at rc
    omega
  · have floor := forest_copy_matching (G \ R) m pm blue
    rw [Fintype.card_fin] at floor
    by_cases noRoom : matchingEdges G < s-1
    · have all := force G le_rfl
      rcases all with fr | fb
      · have orig := forest_copy_matching G n pn fr
        rw [Fintype.card_fin] at orig; omega
      · rw [sdiff_self] at fb
        have empty := forest_copy_matching (⊥ : SimpleGraph X) m pm fb
        rw [Fintype.card_fin,matchingEdges_bot] at empty; omega
    · dsimp [u] at bc; omega

theorem binary_widths {p q : ℕ} (hp : 0<p) (hq : 0<q) (a b : ℕ) :
    widthAt (binaryProfile p a) (binaryProfile q b) 0 2 = p+q-1+max a b ∧
    widthAt (binaryProfile p a) (binaryProfile q b) 0 3 = p+q-1 := by
  let F := binaryProfile p a
  let H := binaryProfile q b
  let R := p+q-1
  have card (h j : ℕ) (fit : j ≤ rowCount (p+a) (q+b) 0)
      (spec : ∀ k<rowCount (p+a) (q+b) 0, h ≤ diagonal F H (k+2) ↔ k<j) :
      widthAt F H 0 h = j := by
    have eq : offsetsAt F H 0 h = Finset.range j := by
      ext k
      simp only [offsetsAt,Finset.mem_filter,Finset.mem_range,Nat.zero_add]
      by_cases live : k<rowCount (p+a) (q+b) 0
      · simp [live,spec k live]
      · simp [live,show ¬k<j by omega]
    rw [widthAt,eq,Finset.card_range]
  have cost (k : ℕ) (live : k<rowCount (p+a) (q+b) 0) :
      diagonal F H (k+2) = (if k<R then 3 else if k<R+max a b then 2 else 1) :=
    binary_diagonal hp hq a b k (by dsimp [rowCount] at live; omega)
  constructor
  · apply card
    · dsimp [rowCount]; omega
    · intro k live; rw [cost k live]; dsimp [R]; split_ifs <;> omega
  · apply card
    · dsimp [rowCount]; omega
    · intro k live; rw [cost k live]; dsimp [R]; split_ifs <;> omega
#print axioms rank_floor_of_splittable
#print axioms binary_widths
end JSP452Audit.StarHost