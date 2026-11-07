import ActualPieceMenu
import SelectedEdgeSaving
import SelectedComponentTotals
import RegionPieceChoice

namespace JSP452Audit.StarHost.DegreeRegion
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X} {D : ℕ} (K : DegreeRegion G D)

/-- Actual original edges inside all selected positive pieces, on X itself. -/
def selectedGraph (T : Finset ↥K.positive) : SimpleGraph X :=
  T.sup (fun c => wholePiece G K.barrier c.val)

theorem selectedGraph_away (T : Finset ↥K.positive) (U : Set X)
    (away : ∀ c ∈ T, ∀ ⦃x y⦄, (wholePiece G K.barrier c.val).Adj x y → x ∉ U) :
    ∀ ⦃x y⦄, (K.selectedGraph T).Adj x y → x ∉ U := by
  classical
  induction T using Finset.induction_on with
  | empty => exact fun _ _ e => False.elim e
  | @insert c t fresh ih =>
      intro x y edge
      change ((insert c t).sup (fun a : ↥K.positive => wholePiece G K.barrier a.val)).Adj x y at edge
      rw [Finset.sup_insert] at edge
      rcases edge with h|h
      · exact away c (Finset.mem_insert_self _ _) h
      · exact ih (fun d hd => away d (Finset.mem_insert_of_mem hd)) h

/-- One and the same induced remainder has the full next row and the exact
original edge saving. No sign or nonemptiness condition is imposed on T. -/
theorem selected_menu_saving (T : Finset ↥K.positive) (U : Set X) {s t r : ℕ}
    (n m : ℕ → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i<s, 0<n i) (pm : ∀ j<t, 0<m j)
    (indep : G.IsIndepSet U) (full : ∀ x ∈ U, Nat.card (G.neighborSet x) = D)
    (away : ∀ c ∈ T, ∀ ⦃x y⦄, (wholePiece G K.barrier c.val).Adj x y → x ∉ U)
    (small : ∀ c ∈ T, K.pieceCapacity c ≤ r+U.ncard+1)
    (row : ForcingRow G s t n m r) :
    let Y := (G \ K.selectedGraph T).induce Uᶜ
    ForcingRow Y s t n m (r+U.ncard+∑ c ∈ T, K.pieceCapacity c) ∧
      (G.edgeSet.ncard : ℤ) = (Y.edgeSet.ncard : ℤ) +
        (D : ℤ) * (U.ncard + (∑ c ∈ T, K.pieceCapacity c) : ℕ) + (∑ c ∈ T, K.pieceWeight c) := by
  classical
  intro Y
  let e : ↥T ↪ (G.induce K.barrierᶜ).ConnectedComponent :=
    (Function.Embedding.subtype (· ∈ T)).trans (Function.Embedding.subtype (· ∈ K.positive))
  let part (c : ↥K.positive) := wholePiece G K.barrier c.val
  let lifted (c : ↥T) := part c.val
  have complete : Finset.univ.sup lifted = K.selectedGraph T := by
    rw [Finset.univ_eq_attach T]
    exact T.sup_attach part
  have caps (V : Finset ↥T) : matchingEdges (V.sup lifted) ≤ ∑ c ∈ V, K.pieceCapacity c.val :=
    (component_totals_on_labels G K.barrier e V D).1.le
  have useRow := actual_piece_menu G U lifted (fun c : ↥T => K.pieceCapacity c.val)
    n m hn hm pn pm (fun c => wholePiece_le _ _ _) caps
    (fun c => small c.val c.property) row
  rw [complete,Finset.sum_coe_sort T K.pieceCapacity] at useRow
  refine ⟨useRow,?_⟩
  have sub : K.selectedGraph T ≤ G := Finset.sup_le (fun _ _ => wholePiece_le _ _ _)
  have phys := selected_edge_saving G (K.selectedGraph T) U D sub indep full (K.selectedGraph_away T U away)
  have acct : ((K.selectedGraph T).edgeSet.ncard : ℤ) =
      (D : ℤ)*(∑ c ∈ T, K.pieceCapacity c : ℕ) + ∑ c ∈ T, K.pieceWeight c :=
    (component_totals_on_labels G K.barrier (Function.Embedding.subtype (· ∈ K.positive)) T D).2
  have priced := congrArg (fun a : ℕ => (a:ℤ)) phys
  change (G.edgeSet.ncard : ℤ) = ↑(Y.edgeSet.ncard + (K.selectedGraph T).edgeSet.ncard + D*U.ncard) at priced
  simp only [Nat.cast_add,Nat.cast_mul,acct] at priced
  rw [Nat.cast_add,mul_add]
  omega

#print axioms selectedGraph_away
#print axioms selected_menu_saving
end JSP452Audit.StarHost.DegreeRegion
