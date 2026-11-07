import ComponentOrderRemovalBudget
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Any feasible pattern loses at most the fixed maximum number of labels.
The complete residual entries therefore dominate the original shifted tail. -/
theorem residual_dominates_shift {s : ℕ} (W : RemovalBudget s) (n : Fin s→ℕ) (hn : Antitone n)
    (i : Fin W.len) : padDemand n (W.loss+i.val)≤W.entries n i := by
  have bound := W.loss_le_order
  have total : W.loss+W.len=s := by dsimp [RemovalBudget.len];omega
  have room : W.loss+i.val<s := by have := i.isLt;omega
  rw [padDemand,dif_pos room]
  apply W.le_entries
  intro T
  apply hn
  let f (z : Fin W.len) : Fin (W.loss+W.len) := ⟨(W.label T z).val,by rw [total];exact (W.label T z).isLt⟩
  have mono : StrictMono f := fun _ _ h => (W.label T).strictMono h
  exact strict_index_offset_le mono i

/-- The e0 removed labels and delta=mu-e0 are computed on the original
core, and the new rank is strictly smaller even when every root is absent. -/
theorem strict_complete_component_exterior {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (paid : AllSmallerPaid.{u} (rowCount s t r))
    (head : n ⟨0,hs⟩≤D) (large : ∃c:(G.induce K.core).ConnectedComponent,D+1≤Nat.card c.supp)
    (pos : 0<matchingEdges (G.induce K.core)) (escaped : matchingEdges (G.induce K.core)<s)
    (d : ℕ) (dpos : 0<d) (original : matchingEdges G+d=rowCount s t r) :
    let μ := matchingEdges (G.induce K.core)
    let a := K.roots.ncard
    let B := G.induce K.rest
    let W := componentBudget (G.induce K.core) n
    1≤W.loss ∧ W.loss≤μ ∧
    ForcingRow B W.len t (padDemand (W.entries n)) (padDemand m) (r+a) ∧
    rowCount W.len t (r+a)=matchingEdges B+d+(μ-W.loss) ∧ rowCount W.len t (r+a)<rowCount s t r ∧
    r+a+d+(μ-W.loss)+1≤min W.len t ∧ max W.len t≤matchingEdges B ∧
    rowEnergy (W.entries n) m (r+a)≤B.edgeSet.ncard := by
  intro μ a B W
  have lo : 1≤W.loss := by
    obtain ⟨c,h⟩ := large
    exact component_budget_accepts_singleton _ n ⟨0,hs⟩ c pos (by omega)
  have hi : W.loss≤μ := component_budget_loss_le _ n
  have live : 0<W.len := by dsimp [RemovalBudget.len];change μ<s at escaped;omega
  have real := fixed_residual_on_exterior G K W n m hn hm pn pm (component_budget_admits _ n pn) row
  have eq := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+matchingEdges B at eq
  have len : W.len+W.loss=s := by dsimp [RemovalBudget.len];change μ<s at escaped;omega
  have rank : rowCount W.len t (r+a)=matchingEdges B+d+(μ-W.loss) := by
    dsimp [rowCount] at original ⊢;omega
  have smaller : rowCount W.len t (r+a)<rowCount s t r := by omega
  have price := positive_exterior_row_price B live ht (W.entries n) m (W.entries_antitone n hn) hm
    (W.entries_positive n pn) pm real paid (by simpa [Nat.add_assoc] using rank) smaller (by omega : 0<d+(μ-W.loss))
  exact ⟨lo,hi,real,rank,smaller,by have := price.2.1;omega,price.2.2,price.1⟩

#print axioms residual_dominates_shift
#print axioms strict_complete_component_exterior
end JSP452Audit.StarHost
