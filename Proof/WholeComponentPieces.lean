import EraseClosedEdges
import HallRegions

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- The labels are the original vertices of this particular residual component. -/
def wholeLabels (G : SimpleGraph X) (S : Set X) (c : (G.induce Sᶜ).ConnectedComponent) : Set X :=
  Subtype.val '' c.supp

/-- Keep each original edge inside c, on the original host vertex type. -/
def wholePiece (G : SimpleGraph X) (S : Set X) (c : (G.induce Sᶜ).ConnectedComponent) :
    SimpleGraph X where
  Adj x y := G.Adj x y ∧ x ∈ wholeLabels G S c ∧ y ∈ wholeLabels G S c
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[simp] theorem wholePiece_adj (G : SimpleGraph X) (S : Set X)
    (c : (G.induce Sᶜ).ConnectedComponent) (x y : X) :
    (wholePiece G S c).Adj x y ↔ G.Adj x y ∧
      x ∈ (Subtype.val '' c.supp : Set X) ∧ y ∈ (Subtype.val '' c.supp : Set X) := Iff.rfl

theorem wholePiece_le (G : SimpleGraph X) (S : Set X) (c : (G.induce Sᶜ).ConnectedComponent) :
    wholePiece G S c ≤ G := fun _ _ h => h.1

private theorem piece_sup_adj {I : Type*} (piece : I → SimpleGraph X) (T : Finset I) (x y : X) :
    (T.sup piece).Adj x y ↔ ∃ c ∈ T, (piece c).Adj x y := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert c T fresh ih =>
    simp only [Finset.sup_insert,SimpleGraph.sup_adj,ih,Finset.mem_insert]
    grind

/-- No edge of the induced region connects different residual components.
The family union is exactly the graph of all original edges inside the region. -/
theorem sup_wholePiece_adj (G : SimpleGraph X) (S : Set X)
    (T : Finset (G.induce Sᶜ).ConnectedComponent) (x y : X) :
    (T.sup (wholePiece G S)).Adj x y ↔
      G.Adj x y ∧ x ∈ regionCore G S (T : Set _) ∧ y ∈ regionCore G S (T : Set _) := by
  rw [piece_sup_adj]
  constructor
  · rintro ⟨c,ct,adj,⟨zx,hx,rfl⟩,⟨zy,hy,rfl⟩⟩
    refine ⟨adj,⟨zx,rfl,?_⟩,⟨zy,rfl,?_⟩⟩
    · exact (show (G.induce Sᶜ).connectedComponentMk zx = c from hx).symm ▸ ct
    · exact (show (G.induce Sᶜ).connectedComponentMk zy = c from hy).symm ▸ ct
  · rintro ⟨adj,⟨zx,rfl,ct⟩,⟨zy,rfl,_⟩⟩
    let c := (G.induce Sᶜ).connectedComponentMk zx
    have rel : (G.induce Sᶜ).Adj zy zx := adj.symm
    exact ⟨c,ct,adj,⟨zx,rfl,rfl⟩,⟨zy,ConnectedComponent.sound rel.reachable,rfl⟩⟩

private theorem sup_wholePiece_restrictions (G : SimpleGraph X) (S : Set X)
    (T : Finset (G.induce Sᶜ).ConnectedComponent) :
    let H := T.sup (wholePiece G S)
    let U := regionCore G S (T : Set _)
    H.induce U = G.induce U ∧ eraseInternal H U = ⊥ ∧
      ∀ x ∈ U, ∀ y ∈ Uᶜ, ¬ H.Adj x y := by
  intro H U
  refine ⟨?_,?_,?_⟩
  · ext x y
    change H.Adj x.val y.val ↔ G.Adj x.val y.val
    exact ⟨fun h => ((sup_wholePiece_adj G S T _ _).mp h).1,
      fun h => (sup_wholePiece_adj G S T _ _).mpr ⟨h,x.property,y.property⟩⟩
  · ext x y
    refine ⟨fun h => ?_,False.elim⟩
    exact h.2 ((sup_wholePiece_adj G S T x y).mp h.1).2
  · intro x _ y hy adj
    exact hy ((sup_wholePiece_adj G S T x y).mp adj).2.2

theorem matchingEdges_sup_wholePiece [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Finset (G.induce Sᶜ).ConnectedComponent) :
    matchingEdges (T.sup (wholePiece G S)) = matchingEdges (G.induce (regionCore G S (T : Set _))) := by
  obtain ⟨same,empty,sep⟩ := sup_wholePiece_restrictions G S T
  have count := erase_closed_matching_rank _ _ sep
  simpa only [empty,matchingEdges_bot,Nat.zero_add,same] using count

theorem edgeCount_sup_wholePiece [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Finset (G.induce Sᶜ).ConnectedComponent) :
    (T.sup (wholePiece G S)).edgeSet.ncard = (G.induce (regionCore G S (T : Set _))).edgeSet.ncard := by
  obtain ⟨same,empty,_⟩ := sup_wholePiece_restrictions G S T
  have count := erase_internal_edge_count (T.sup (wholePiece G S)) (regionCore G S (T : Set _))
  simpa only [empty,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.zero_add,same] using count

#print axioms sup_wholePiece_adj
#print axioms matchingEdges_sup_wholePiece
#print axioms edgeCount_sup_wholePiece
end JSP452Audit.StarHost
