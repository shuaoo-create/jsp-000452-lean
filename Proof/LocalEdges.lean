import AvailableSlots
import GreedyIndex
import PairFamily

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

abbrev Spec.MustIndex (F : SimpleGraph V) (v : V) :=
  Fin (min (Nat.card (P.Available F v)) (P.mandatoryCount v))

abbrev Spec.MayIndex (F : SimpleGraph V) (v : V) :=
  Fin (min (Nat.card (P.Available F v) - min (Nat.card (P.Available F v)) (P.mandatoryCount v))
    (P.optionalCount v))

/-- One named edge for each local greedy pair of either kind, over every owner. -/
abbrev Spec.LocalIndex (F : SimpleGraph V) :=
  (v : V) × (P.MustIndex F v ⊕ P.MayIndex F v)

noncomputable abbrev Spec.localChoice (F : SimpleGraph V) (v : V) :=
  greedyIndex (P.Available F v) (P.mandatoryCount v) (P.optionalCount v)

noncomputable def Spec.localLeft (F : SimpleGraph V) : P.LocalIndex F ↪ P.Vertex :=
  (Function.Embedding.sigmaMap (Function.Embedding.refl V)
    (fun v => (P.localChoice F v).allSlots)).trans (P.availableAt F)

noncomputable def Spec.localRightToken (F : SimpleGraph V) : P.LocalIndex F ↪ P.Token :=
  let byOwner : P.LocalIndex F ↪ Σ v, Fin (P.mandatoryCount v) ⊕ Fin (P.optionalCount v) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl V)
      (fun v => (P.localChoice F v).mandatoryToken.sumMap (P.localChoice F v).optionalToken)
  (byOwner.trans (Equiv.sigmaSumDistrib (fun v => Fin (P.mandatoryCount v))
    (fun v => Fin (P.optionalCount v))).toEmbedding).trans Function.Embedding.inl

noncomputable def Spec.localRight (F : SimpleGraph V) : P.LocalIndex F ↪ P.Vertex :=
  (P.localRightToken F).trans Function.Embedding.inr

@[simp] theorem Spec.localLeft_mandatory (F : SimpleGraph V) (v : V) (i : P.MustIndex F v) :
    P.localLeft F ⟨v, .inl i⟩ =
      P.availableAt F ⟨v, (P.localChoice F v).mandatorySlot i⟩ := rfl

@[simp] theorem Spec.localLeft_optional (F : SimpleGraph V) (v : V) (i : P.MayIndex F v) :
    P.localLeft F ⟨v, .inr i⟩ =
      P.availableAt F ⟨v, (P.localChoice F v).optionalSlot i⟩ := rfl

@[simp] theorem Spec.localRight_mandatory (F : SimpleGraph V) (v : V) (i : P.MustIndex F v) :
    P.localRight F ⟨v, .inl i⟩ =
      P.mandatory ⟨v, (P.localChoice F v).mandatoryToken i⟩ := rfl

@[simp] theorem Spec.localRight_optional (F : SimpleGraph V) (v : V) (i : P.MayIndex F v) :
    P.localRight F ⟨v, .inr i⟩ =
      P.optional ⟨v, (P.localChoice F v).optionalToken i⟩ := rfl

theorem Spec.localPair_adj (F : SimpleGraph V) :
    ∀ i : P.LocalIndex F, P.graph.Adj (P.localLeft F i) (P.localRight F i) := by
  rintro ⟨v, i | j⟩ <;> exact rfl

theorem Spec.localEndpointRanges_disjoint (F : SimpleGraph V) :
    Disjoint (Set.range (P.localLeft F)) (Set.range (P.localRight F)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, impossible⟩
  change (Sum.inr (P.localRightToken F j) : P.Vertex) =
    .inl ⟨i.1, ((P.localChoice F i.1).allSlots i.2).val⟩ at impossible
  cases impossible

/-- Use the available stubs for mandatory tokens first and optional tokens next. -/
noncomputable def Spec.localLift (F : SimpleGraph V) : P.graph.Subgraph :=
  pairFamily P.graph (P.localLeft F) (P.localRight F) (P.localPair_adj F)

@[simp] theorem Spec.localLift_verts (F : SimpleGraph V) :
    (P.localLift F).verts = Set.range (P.localLeft F) ∪ Set.range (P.localRight F) := rfl

theorem Spec.localLift_isMatching (F : SimpleGraph V) : (P.localLift F).IsMatching :=
  pairFamily_isMatching P.graph (P.localLeft F) (P.localRight F) (P.localPair_adj F)
    (P.localEndpointRanges_disjoint F)

theorem Spec.crossLift_disjoint_localLift (F : SimpleGraph V) :
    Disjoint (P.crossLift F).verts (P.localLift F).verts := by
  rw [Set.disjoint_left]
  rintro _ hx (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact P.availableAt_not_in_cross F ⟨i.1,(P.localChoice F i.1).allSlots i.2⟩ hx
  · exact P.token_not_mem_crossLift F (P.localRightToken F i) hx

#print axioms Spec.localLift
#print axioms Spec.localPair_adj
#print axioms Spec.localLift_isMatching
#print axioms Spec.localLift_verts
#print axioms Spec.crossLift_disjoint_localLift
end JSP452Audit.Padded
