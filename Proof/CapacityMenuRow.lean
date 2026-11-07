import CapacitySplit
import RestorePieceColor
import TrimTouchedForest
import RegionForcing
namespace JSP452Audit.StarHost
open SimpleGraph
/-- Erasing the chosen pieces preserves a full row, not just a single pair.
Different pairs may use different partitions of the same original pieces. -/
theorem capacity_menu_row {I X : Type*} [Fintype I] [Finite X]
    (G Y : SimpleGraph X) (part : I → SimpleGraph X) (z : I → ℕ) {r s t : ℕ}
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (hY : Y≤G) (sub : ∀ k, part k≤G) (cover : G≤Y⊔(Finset.univ.sup part))
    (cost : ∀ T : Finset I, matchingEdges (T.sup part) ≤ ∑ k∈T,z k)
    (small : ∀ k, z k ≤ r+1) (row : ForcingRow G s t n m r) :
    ForcingRow Y s t n m (r+∑ k,z k) := by
  classical
  intro i j l q ij il jq hl hq R incl
  obtain ⟨T,rx,by',total⟩ := capacity_split z i j r ij small
  let x := ∑ k∈T,z k
  let y := ∑ k∈Tᶜ,z k
  let i0 := i-x
  let j0 := j-y
  have xi : i0+x=i := Nat.sub_add_cancel rx
  have yj : j0+y=j := Nat.sub_add_cancel by'
  have totals : x+y = ∑ k,z k := total
  have old := row i0 j0 (x+l) (y+q) (by omega) (by omega) (by omega) (by omega) (by omega)
  have cover' : G≤(Y⊔T.sup part)⊔Tᶜ.sup part := by
    rw [sup_pieces_split part T,← sup_assoc] at cover
    exact cover
  rcases restored_pair_outcome G Y (T.sup part) (Tᶜ.sup part) hY
    (Finset.sup_le (fun k _ => sub k)) cover' _ _ old R incl with red | blue
  · exact Or.inl (xi ▸ trim_touched_forest R (T.sup part) n hn i0 x l (cost T) red)
  · exact Or.inr (yj ▸ trim_touched_forest (Y \ R) (Tᶜ.sup part) m hm j0 y q (cost _) blue)
#print axioms capacity_menu_row
end JSP452Audit.StarHost