import MatchingShadow
import CliquePairs
import PairFamily

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Only optional and global tokens not used by the original matching. -/
abbrev Spec.FreePool (M : P.graph.Subgraph) :=
  {t : P.Token // P.inPool t ∧ (Sum.inr t : P.Vertex) ∉ M.verts}

/-- Interface for using the completed matching without exposing the chosen pairing. -/
structure Spec.IsPoolCompletion (M N : P.graph.Subgraph) : Prop where
  matching : N.IsMatching
  extendsOriginal : M ≤ N
  poolCovered : ∀ t : P.Token, P.inPool t → (Sum.inr t : P.Vertex) ∈ N.verts
  stub_mem_iff : ∀ s : P.Stub, (Sum.inl s : P.Vertex) ∈ N.verts ↔
    (Sum.inl s : P.Vertex) ∈ M.verts
  mandatory_mem_iff : ∀ a : P.Mandatory, P.mandatory a ∈ N.verts ↔ P.mandatory a ∈ M.verts
  shadow_eq : P.redShadow N = P.redShadow M
  newEdgeEndpoints : ∀ {x y : P.Vertex}, N.Adj x y → ¬ M.Adj x y →
    ∃ i j : P.FreePool M, (Sum.inr i.val : P.Vertex) = x ∧ (Sum.inr j.val : P.Vertex) = y

theorem Spec.exists_poolCompletion (M : P.graph.Subgraph) (hM : M.IsMatching)
    (even : Even (Nat.card (P.FreePool M))) :
    ∃ N : P.graph.Subgraph, P.IsPoolCompletion M N := by
  classical
  let e : P.FreePool M ↪ P.Vertex :=
    ⟨fun i => .inr i.val, fun _ _ h => Subtype.ext (Sum.inr.inj h)⟩
  have clique : ∀ ⦃i j : P.FreePool M⦄, i ≠ j → P.graph.Adj (e i) (e j) := by
    intro i j h
    exact ⟨i.property.1, j.property.1, fun hij => h (Subtype.ext hij)⟩
  obtain ⟨C, hC, verts⟩ := existsMatchingOnEvenClique P.graph e clique even
  have fromC {x : P.Vertex} (hx : x ∈ C.verts) : ∃ i : P.FreePool M, e i = x := by
    rw [verts] at hx
    exact hx
  have apart : Disjoint M.verts C.verts := by
    apply Set.disjoint_left.mpr
    intro x hx hcx
    obtain ⟨i, rfl⟩ := fromC hcx
    exact i.property.2 hx
  have noStub (s : P.Stub) : (Sum.inl s : P.Vertex) ∉ C.verts := by
    intro hs
    obtain ⟨i, hi⟩ := fromC hs
    cases hi
  have noMand (a : P.Mandatory) : P.mandatory a ∉ C.verts := by
    intro ha
    obtain ⟨i, hi⟩ := fromC ha
    have same : i.val = (.inl (.inl a) : P.Token) := Sum.inr.inj hi
    have pooled := i.property.1
    rw [same] at pooled
    exact pooled
  refine ⟨M ⊔ C, matching_sup_of_disjoint_verts P.graph hM hC apart, le_sup_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    by_cases used : (Sum.inr t : P.Vertex) ∈ M.verts
    · exact Or.inl used
    · apply Or.inr
      rw [verts]
      exact ⟨⟨t, ht, used⟩, rfl⟩
  · intro s
    exact ⟨fun hs => hs.elim id (fun hc => (noStub s hc).elim), Or.inl⟩
  · intro a
    exact ⟨fun ha => ha.elim id (fun hc => (noMand a hc).elim), Or.inl⟩
  · ext v w
    constructor
    · rintro ⟨edge, h | h⟩
      · exact ⟨edge, h⟩
      · exact (noStub ⟨v, .inl ⟨w, edge⟩⟩ (C.edge_vert h)).elim
    · rintro ⟨edge, h⟩
      exact ⟨edge, Or.inl h⟩
  · intro x y hxy old
    have hc : C.Adj x y := hxy.resolve_left old
    obtain ⟨i, hi⟩ := fromC (C.edge_vert hc)
    obtain ⟨j, hj⟩ := fromC (C.edge_vert hc.symm)
    exact ⟨i, j, hi, hj⟩

#print axioms Spec.exists_poolCompletion
end JSP452Audit.Padded
