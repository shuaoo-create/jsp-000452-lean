import OriginalUpper

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The host part of the edge-coloring quantifier in the pinned sizeRamsey definition. -/
def Forces {X A B : Type*} (G : SimpleGraph X) (T : SimpleGraph A) (S : SimpleGraph B) : Prop :=
  ∀ R : SimpleGraph X, R ≤ G → T.IsContained R ∨ S.IsContained (G \ R)

/-- The red/blue roles can be interchanged in this exact host. -/
theorem forces_swap {X A B : Type*} {G : SimpleGraph X} {T : SimpleGraph A} {S : SimpleGraph B}
    (h : Forces G T S) : Forces G S T := by
  intro R hR
  have diffSub : G \ R ≤ G := fun _ _ he => he.1
  have invol : G \ (G \ R) = R := by
    ext i j
    change (G.Adj i j ∧ ¬(G.Adj i j ∧ ¬R.Adj i j)) ↔ R.Adj i j
    constructor
    · rintro ⟨hg,hr⟩
      by_contra nr
      exact hr ⟨hg,nr⟩
    · intro r
      exact ⟨hR r,fun z => z.2 r⟩
  rcases h _ diffSub with t | s
  · exact Or.inr t
  · exact Or.inl (invol ▸ s)

#print axioms forces_swap
end JSP452Audit.StarHost
