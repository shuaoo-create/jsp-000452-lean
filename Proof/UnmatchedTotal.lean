import RedExcess
import BlueExcess

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

private abbrev FreeMandatory (M : P.graph.Subgraph) (v : V) :=
  {i : Fin (P.mandatoryCount v) // P.mandatory ⟨v,i⟩ ∉ M.verts}

private abbrev FreeStub (M : P.graph.Subgraph) (v : V) :=
  {i : P.G.neighborSet v ⊕ Fin (P.padding v) // (Sum.inl (⟨v,i⟩ : P.Stub) : P.Vertex) ∉ M.verts}

private abbrev Measured (M : P.graph.Subgraph) :=
  (Σ v, FreeMandatory P M v) ⊕ (Σ v, FreeStub P M v)

private def toFreeVertex (M : P.graph.Subgraph) :
    Measured P M → {x : P.Vertex // x ∉ M.verts}
  | .inl ⟨v,i⟩ => ⟨P.mandatory ⟨v,i.val⟩, i.property⟩
  | .inr ⟨v,i⟩ => ⟨.inl ⟨v,i.val⟩, i.property⟩

private def fromFreeVertex (M : P.graph.Subgraph) :
    {x : P.Vertex // x ∉ M.verts} → Option (Measured P M)
  | ⟨.inl ⟨v,i⟩,h⟩ => some (.inr ⟨v,⟨i,h⟩⟩)
  | ⟨.inr (.inl (.inl ⟨v,i⟩)),h⟩ => some (.inl ⟨v,⟨i,h⟩⟩)
  | ⟨.inr (.inl (.inr _)),_⟩ | ⟨.inr (.inr _),_⟩ => none

private theorem measuredBound (M : P.graph.Subgraph) :
    (∑ v, (Nat.card (FreeMandatory P M v) + Nat.card (FreeStub P M v))) ≤
      Nat.card {x : P.Vertex // x ∉ M.verts} := by
  classical
  have decode : ∀ a, fromFreeVertex P M (toFreeVertex P M a) = some a := by
    rintro (⟨v,⟨i,hi⟩⟩ | ⟨v,⟨i,hi⟩⟩) <;> rfl
  have inj : Function.Injective (toFreeVertex P M) := by
    intro a b h
    exact Option.some.inj ((decode a).symm.trans ((congrArg (fromFreeVertex P M) h).trans (decode b)))
  have hc := Nat.card_le_card_of_injective _ inj
  simpa only [Measured, Nat.card_sum, Nat.card_sigma, Finset.sum_add_distrib] using hc

/-- Every matching projects to a red graph whose total excess over the two local caps
    is bounded by the actual number of unmatched vertices of the auxiliary graph. -/
theorem Spec.shadowDeviation_le_unmatched (M : P.graph.Subgraph) (hM : M.IsMatching)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    (∑ v, ((Nat.card ((P.redShadow M).neighborSet v) - P.A v) +
      (P.G.degree v - Nat.card ((P.redShadow M).neighborSet v) - P.B v))) ≤
      Nat.card {x : P.Vertex // x ∉ M.verts} := by
  apply le_trans _ (measuredBound P M)
  exact Finset.sum_le_sum fun v _ => Nat.add_le_add
    (P.redExcess_le_unmatchedMandatory M hM v) (P.blueExcess_le_unmatchedStubs M hM v (caps v))

#print axioms Spec.shadowDeviation_le_unmatched

end JSP452Audit.Padded
