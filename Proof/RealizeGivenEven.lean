import LocalMustSupport
import LocalSlotSupport
import PoolComplete

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Given any original red subgraph, an even residual pool suffices for *attaining*
    its exact red and blue total excess with a real matching and the same red edges. -/
theorem Spec.realize_given_even (F : SimpleGraph V) (hF : F ≤ P.G)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v)
    (even : Even (Nat.card (P.FreePool (P.crossLift F ⊔ P.localLift F)))) :
    ∃ N : P.graph.Subgraph, N.IsMatching ∧ P.redShadow N = F ∧
      Nat.card {x : P.Vertex // x ∉ N.verts} =
        ∑ v, ((Nat.card (F.neighborSet v) - P.A v) +
          (P.G.degree v - Nat.card (F.neighborSet v) - P.B v)) := by
  classical
  let M := P.crossLift F ⊔ P.localLift F
  have hM : M.IsMatching := matching_sup_of_disjoint_verts P.graph
    (P.crossLift_isMatching F) (P.localLift_isMatching F) (P.crossLift_disjoint_localLift F)
  obtain ⟨N,hN⟩ := P.exists_poolCompletion M hM even
  refine ⟨N,hN.matching,hN.shadow_eq.trans (P.beforePool_shadow F hF),?_⟩
  rw [P.card_free_of_pool_covered N hN.poolCovered]
  apply Finset.sum_congr rfl
  intro v _
  let p := P.localChoice F v
  have must : Nat.card (P.FreeMust N v) =
      Nat.card {i : Fin (P.mandatoryCount v) // i ∉ Set.range p.mandatoryToken} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun i =>
      ((hN.mandatory_mem_iff ⟨v,i⟩).trans (P.beforePool_mandatory_mem F v i)).not)
  have slots : Nat.card (P.FreeSlot N v) =
      Nat.card {a : P.Available F v // a ∉ Set.range p.allSlots} := by
    apply Nat.card_congr
    exact (Equiv.subtypeEquivRight (fun i => (hN.stub_mem_iff ⟨v,i⟩).not)).trans
      (P.beforePool_slotEquiv F v)
  rw [must, slots]
  exact P.greedy_leftovers F hF v (caps v) p

#print axioms Spec.realize_given_even

end JSP452Audit.Padded
