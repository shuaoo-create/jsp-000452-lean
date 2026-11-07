import LocalEdges

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- A mandatory token is covered exactly when the greedy step selects its index. -/
theorem Spec.beforePool_mandatory_mem (F : SimpleGraph V) (v : V)
    (i : Fin (P.mandatoryCount v)) :
    P.mandatory ⟨v, i⟩ ∈ (P.crossLift F ⊔ P.localLift F).verts ↔
      i ∈ Set.range (P.localChoice F v).mandatoryToken := by
  constructor
  · rintro (hx | (⟨k, hk⟩ | ⟨⟨u, k | k⟩, hk⟩))
    · exact (P.token_not_mem_crossLift F _ hx).elim
    · change (Sum.inl _ : P.Vertex) = .inr _ at hk
      cases hk
    · have hs : (⟨u, (P.localChoice F u).mandatoryToken k⟩ : P.Mandatory) = ⟨v, i⟩ :=
        Sum.inl.inj (Sum.inl.inj (Sum.inr.inj hk))
      have hv : u = v := congrArg Sigma.fst hs
      subst u
      exact ⟨k, eq_of_heq (Sigma.mk.inj hs).2⟩
    · have no := Sum.inl.inj (Sum.inr.inj hk)
      cases no
  · rintro ⟨k, rfl⟩
    exact Or.inr (Or.inr ⟨⟨v, .inl k⟩, rfl⟩)

/-- Local edges always meet a token, so they add no projected original edge. -/
theorem Spec.beforePool_shadow (F : SimpleGraph V) (hF : F ≤ P.G) :
    P.redShadow (P.crossLift F ⊔ P.localLift F) = F := by
  ext v w
  constructor
  · rintro ⟨e, hx | hl⟩
    · exact hx.1
    · obtain ⟨k, _, bad⟩ | ⟨k, bad, _⟩ := hl
      all_goals
        change (Sum.inr _ : P.Vertex) = .inl _ at bad
        cases bad
  · intro h
    exact ⟨hF h, Or.inl ⟨h, rfl⟩⟩

#print axioms Spec.beforePool_mandatory_mem
#print axioms Spec.beforePool_shadow
end JSP452Audit.Padded
