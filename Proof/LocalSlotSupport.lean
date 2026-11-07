import PoolCounts
import LocalEdges

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

private theorem slotInLocal (F : SimpleGraph V) (v : V) (a : P.Available F v) :
    (.inl (⟨v,a.val⟩ : P.Stub) : P.Vertex) ∈ (P.localLift F).verts ↔
      a ∈ Set.range (P.localChoice F v).allSlots := by
  constructor
  · rintro (⟨⟨w,i⟩,eq⟩ | ⟨i,eq⟩)
    · change P.availableAt F ⟨w,(P.localChoice F w).allSlots i⟩ = P.availableAt F ⟨v,a⟩ at eq
      have same := (P.availableAt F).injective eq
      have base : w = v := congrArg Sigma.fst same
      subst w
      exact ⟨i, eq_of_heq (Sigma.mk.inj_iff.mp same).2⟩
    · change (Sum.inr _ : P.Vertex) = Sum.inl _ at eq
      cases eq
  · rintro ⟨i,rfl⟩
    exact Or.inl ⟨⟨v,i⟩,rfl⟩

/-- An unmatched local slot is precisely an unused entry of the greedy slot
    embedding among the positions that survived the cross matching. -/
def Spec.beforePool_slotEquiv (F : SimpleGraph V) (v : V) :
    P.FreeSlot (P.crossLift F ⊔ P.localLift F) v ≃
      {a : P.Available F v // a ∉ Set.range (P.localChoice F v).allSlots} where
  toFun a := by
    let b : P.Available F v := ⟨a.val, fun hc => a.property (Or.inl hc)⟩
    exact ⟨b,fun h => a.property (Or.inr ((slotInLocal P F v b).mpr h))⟩
  invFun b := ⟨b.val.val, fun h =>
    h.elim b.val.property (fun hl => b.property ((slotInLocal P F v b.val).mp hl))⟩
  left_inv _ := rfl
  right_inv _ := rfl

#print axioms Spec.beforePool_slotEquiv

end JSP452Audit.Padded
