import RowDelete
import HostIsoRow

namespace JSP452Audit.StarHost

/-- Delete any finite set of original vertices. The induced graph still uses
the original surviving labels, and each removed vertex advances the suffix
row once. No order or finiteness assumption on the host type is needed. -/
theorem row_delete_finset {X : Type*} {s t r : ℕ}
    (G : SimpleGraph X) (U : Finset X) (n m : ℕ → ℕ)
    (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, i < s → 0 < n i) (pm : ∀ j, j < t → 0 < m j)
    (row : ForcingRow G s t n m r) :
    ForcingRow (G.induce {x | x ∉ U}) s t n m (r + U.card) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    simpa only [Finset.card_empty, Nat.add_zero] using
      forcingRow_of_iso (induce_delete_empty_iso G) row
  | @insert v U hv ih =>
    let base := G.induce {x | x ∉ U}
    let point : {x : X // x ∉ U} := ⟨v, hv⟩
    have step := row_delete_one base point n m hn hm pn pm ih
    have transported := forcingRow_of_iso (induce_delete_insert_iso G U v hv) step
    simpa only [Finset.card_insert_of_notMem hv, Nat.add_assoc] using transported

#print axioms row_delete_finset
end JSP452Audit.StarHost
