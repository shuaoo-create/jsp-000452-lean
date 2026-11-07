import MatchingShadow
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

private abbrev LocalStubs (v : V) := P.G.neighborSet v ⊕ Fin (P.padding v)

private def atStub (v : V) (i : LocalStubs P v) : P.Vertex :=
  .inl (⟨v, i⟩ : P.Stub)

private abbrev PossibleMate (M : P.graph.Subgraph) (v : V) :=
  (P.redShadow M).neighborSet v ⊕ (Fin (P.mandatoryCount v) ⊕ Fin (P.optionalCount v))

private def vertexOfMate (M : P.graph.Subgraph) (v : V) : PossibleMate P M v → P.Vertex
  | .inl w => P.realStub w.val v (P.redShadow_le M w.property).symm
  | .inr (.inl j) => P.mandatory ⟨v, j⟩
  | .inr (.inr j) => P.optional ⟨v, j⟩

/-- The actual mate of a used stub has to occupy one of these counted positions. -/
private theorem existsMate (M : P.graph.Subgraph) (hM : M.IsMatching)
    (v : V) (i : LocalStubs P v) (hi : atStub P v i ∈ M.verts) :
    ∃ b : PossibleMate P M v, M.Adj (atStub P v i) (vertexOfMate P M v b) := by
  obtain ⟨y, hadj, _⟩ := hM hi
  cases y with
  | inl t =>
    obtain ⟨u, z | j⟩ := t
    · obtain ⟨z, hz⟩ := z
      cases i with
      | inl w =>
        obtain ⟨w, hw⟩ := w
        have h := (P.real_adj_real_iff hw hz).mp (M.adj_sub hadj)
        obtain ⟨hv, hu⟩ := h
        subst z
        subst u
        have red := (P.redShadow_adj_iff M hw).mpr hadj
        exact ⟨.inl ⟨w, red⟩, hadj⟩
      | inr j => exact (M.adj_sub hadj).elim
    · cases i <;> exact (M.adj_sub hadj).elim
  | inr t =>
    rcases t with (⟨u, j⟩ | ⟨u, k⟩) | g
    · have heq : u = v := (P.stub_adj_mandatory_iff ⟨v,i⟩ ⟨u,j⟩).mp (M.adj_sub hadj)
      subst u
      exact ⟨.inr (.inl j), hadj⟩
    · have heq : u = v := (P.stub_adj_optional_iff ⟨v,i⟩ ⟨u,k⟩).mp (M.adj_sub hadj)
      subst u
      exact ⟨.inr (.inr k), hadj⟩
    · exact False.elim (P.not_stub_adj_global ⟨v,i⟩ g (M.adj_sub hadj))

private theorem usedStubCount_le (M : P.graph.Subgraph) (hM : M.IsMatching) (v : V) :
    Nat.card {i : LocalStubs P v // atStub P v i ∈ M.verts} ≤
      Nat.card ((P.redShadow M).neighborSet v) + (P.mandatoryCount v + P.optionalCount v) := by
  classical
  let used := {i : LocalStubs P v // atStub P v i ∈ M.verts}
  let dest (i : used) : PossibleMate P M v := (existsMate P M hM v i.val i.property).choose
  have edge (i : used) : M.Adj (atStub P v i.val) (vertexOfMate P M v (dest i)) :=
    (existsMate P M hM v i.val i.property).choose_spec
  have inj : Function.Injective dest := by
    intro i j eq
    have hi := edge i
    rw [eq] at hi
    have eqStub := hM.eq_of_adj_right hi (edge j)
    apply Subtype.ext
    simpa [atStub] using eqStub
  have bound := Nat.card_le_card_of_injective dest inj
  simpa only [used, PossibleMate, Nat.card_sum, Nat.card_fin] using bound

/-- Blue excess forces unmatched stubs at this specific original vertex. -/
theorem Spec.blueExcess_le_unmatchedStubs (M : P.graph.Subgraph) (hM : M.IsMatching)
    (v : V) (caps : P.G.degree v ≤ P.A v + P.B v) :
    P.G.degree v - Nat.card ((P.redShadow M).neighborSet v) - P.B v ≤
      Nat.card {i : P.G.neighborSet v ⊕ Fin (P.padding v) //
        (Sum.inl (⟨v,i⟩ : P.Stub) : P.Vertex) ∉ M.verts} := by
  classical
  let used (i : LocalStubs P v) := atStub P v i ∈ M.verts
  change _ ≤ Nat.card {i : LocalStubs P v // ¬ used i}
  have split : Nat.card {i : LocalStubs P v // ¬ used i} =
      Nat.card (LocalStubs P v) - Nat.card {i : LocalStubs P v // used i} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have size : Nat.card (LocalStubs P v) = P.G.degree v + P.padding v := by
    rw [Nat.card_sum, Nat.card_fin, Nat.card_eq_fintype_card, P.G.card_neighborSet_eq_degree]
  have bound : Nat.card {i : LocalStubs P v // used i} ≤
      Nat.card ((P.redShadow M).neighborSet v) + (P.mandatoryCount v + P.optionalCount v) :=
    usedStubCount_le P M hM v
  rw [split,size]
  simp only [Spec.mandatoryCount, Spec.optionalCount, Spec.padding] at bound ⊢
  omega

#print axioms Spec.blueExcess_le_unmatchedStubs
end JSP452Audit.Padded
