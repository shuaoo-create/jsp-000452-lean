import CapacityMenuRow
import RegionSplitRank

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Induction to actual surviving labels commutes with any finite union of pieces. -/
theorem induce_sup_pieces {I X : Type*} (part : I → SimpleGraph X) (V : Set X) (T : Finset I) :
    T.sup (fun k => (part k).induce V) = (T.sup part).induce V := by
  classical
  induction T using Finset.induction_on with
  | empty => rfl
  | @insert k T fresh ih =>
    rw [Finset.sup_insert,Finset.sup_insert,ih]
    rfl

/-- Delete U and erase all selected graph pieces on the surviving vertex type.
Piece budgets from the original graph suffice for every split of the menu. -/
theorem actual_piece_menu {I X : Type*} [Fintype I] [Finite X]
    (G : SimpleGraph X) (U : Set X) (part : I → SimpleGraph X) (z : I → ℕ) {r s t : ℕ}
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i<s, 0<n i) (pm : ∀ j<t, 0<m j)
    (sub : ∀ k, part k ≤ G) (cost : ∀ T : Finset I, matchingEdges (T.sup part) ≤ ∑ k∈T,z k)
    (small : ∀ k, z k ≤ r + U.ncard + 1) (row : ForcingRow G s t n m r) :
    ForcingRow ((G \ Finset.univ.sup part).induce Uᶜ) s t n m (r+U.ncard+∑ k,z k) := by
  let H := G.induce Uᶜ
  let Y := (G \ Finset.univ.sup part).induce Uᶜ
  let inner (k : I) := (part k).induce Uᶜ
  apply capacity_menu_row H Y inner z n m hn hm
  · exact fun _ _ h => h.1
  · exact fun k _ _ h => sub k h
  · intro x y h
    by_cases edge : (Finset.univ.sup part).Adj x.val y.val
    · right
      change (Finset.univ.sup (fun k => (part k).induce Uᶜ)).Adj x y
      rw [induce_sup_pieces]
      exact edge
    · exact Or.inl ⟨h,edge⟩
  · intro T
    change matchingEdges (T.sup (fun k => (part k).induce Uᶜ)) ≤ _
    rw [induce_sup_pieces]
    exact (rank_mono_embedding (SimpleGraph.Embedding.induce (G := T.sup part) Uᶜ)).trans (cost T)
  · exact small
  · exact row_delete_set G U n m hn hm pn pm row

#print axioms induce_sup_pieces
#print axioms actual_piece_menu
end JSP452Audit.StarHost
