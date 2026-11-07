import MatchingShadow

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Selected vertices are precisely the real half-edges of the red graph. -/
def Spec.crossSelected (F : SimpleGraph V) : P.Vertex → Prop
  | .inl ⟨v, .inl w⟩ => F.Adj v w.val
  | _ => False

/-- Reverse a real half-edge. The value at other vertices will not be used by the lift. -/
def Spec.crossMate : P.Vertex → P.Vertex
  | .inl ⟨v, .inl w⟩ => P.realStub w.val v w.property.symm
  | x => x

private theorem selectedMate (F : SimpleGraph V) {x : P.Vertex} (h : P.crossSelected F x) :
    P.crossSelected F (P.crossMate x) ∧ P.crossMate (P.crossMate x) = x ∧
      P.graph.Adj x (P.crossMate x) := by
  rcases x with (⟨v, w | i⟩ | t)
  · exact ⟨(show F.Adj v w.val from h).symm, rfl, ⟨rfl, rfl⟩⟩
  · exact False.elim h
  · exact False.elim h

/-- Lift the edges of F to their disjoint cross pairs. Its vertex set is their actual
support, so a dummy stub, a token, or an unselected real stub is never marked as matched. -/
def Spec.crossLift (F : SimpleGraph V) : P.graph.Subgraph where
  verts := {x | P.crossSelected F x}
  Adj x y := P.crossSelected F x ∧ y = P.crossMate x
  adj_sub := by
    rintro x y ⟨h, rfl⟩
    exact (selectedMate P F h).2.2
  edge_vert := fun h => h.1
  symm := ⟨by
    rintro x y ⟨h, rfl⟩
    exact ⟨(selectedMate P F h).1, (selectedMate P F h).2.1.symm⟩⟩

theorem Spec.crossLift_isMatching (F : SimpleGraph V) : (P.crossLift F).IsMatching := by
  intro x hx
  exact ⟨P.crossMate x, ⟨hx, rfl⟩, fun _ h => h.2⟩

@[simp] theorem Spec.realStub_mem_crossLift_iff (F : SimpleGraph V) {v w : V}
    (e : P.G.Adj v w) : P.realStub v w e ∈ (P.crossLift F).verts ↔ F.Adj v w := Iff.rfl

@[simp] theorem Spec.extraStub_not_mem_crossLift (F : SimpleGraph V) (v : V)
    (i : Fin (P.padding v)) : P.extraStub v i ∉ (P.crossLift F).verts := id

@[simp] theorem Spec.token_not_mem_crossLift (F : SimpleGraph V) (t : P.Token) :
    (.inr t : P.Vertex) ∉ (P.crossLift F).verts := id

/-- From a real incidence, the only possible neighbor in the lift is its opposite. -/
theorem Spec.crossLift_adj_real_iff (F : SimpleGraph V) {v w : V}
    (e : P.G.Adj v w) (x : P.Vertex) :
    (P.crossLift F).Adj (P.realStub v w e) x ↔
      F.Adj v w ∧ x = P.realStub w v e.symm := Iff.rfl

/-- Projecting the lifted cross matching recovers the red subgraph exactly. -/
theorem Spec.redShadow_crossLift (F : SimpleGraph V) (hF : F ≤ P.G) :
    P.redShadow (P.crossLift F) = F := by
  ext v w
  constructor
  · rintro ⟨e, h⟩
    exact (P.crossLift_adj_real_iff F e _).mp h |>.1
  · intro h
    exact ⟨hF h, h, rfl⟩

#print axioms Spec.crossLift
#print axioms Spec.crossLift_isMatching
#print axioms Spec.realStub_mem_crossLift_iff
#print axioms Spec.extraStub_not_mem_crossLift
#print axioms Spec.token_not_mem_crossLift
#print axioms Spec.crossLift_adj_real_iff
#print axioms Spec.redShadow_crossLift
end JSP452Audit.Padded
