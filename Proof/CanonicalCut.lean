import ExtremaBoundary
import PadNeighbors
namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- The canonical retained auxiliary vertices: remove the stub side at S,
    the token side at T, and retain every global parity token. -/
def Spec.keptBy (S T : Set V) : P.Vertex → Prop
  | .inl u => u.1 ∉ S
  | .inr (.inl (.inl u)) => u.1 ∉ T
  | .inr (.inl (.inr u)) => u.1 ∉ T
  | .inr (.inr _) => True

noncomputable def Spec.canonicalKept (S T : Set V) : Finset P.Vertex := by
  classical
  exact Finset.univ.filter (P.keptBy S T)

@[simp] theorem Spec.mem_canonicalKept (S T : Set V) (z : P.Vertex) :
    z ∈ P.canonicalKept S T ↔ P.keptBy S T z := by
  classical
  simp [Spec.canonicalKept]

/-- A maximum-score cut has the canonical form of two disjoint original
    vertex sets. There is no assumption on the input auxiliary cut. -/
theorem Spec.canonical_max_score :
    ∃ S T : Set V, Disjoint S T ∧ ∀ U : Finset P.Vertex,
      retainedScore P.graph U ≤ retainedScore P.graph (P.canonicalKept S T) := by
  classical
  obtain ⟨W,best,blocked⟩ := maximal_cut_obstruction P.graph
  let S : Set V := {v | ¬∃ u : P.Stub, u.1=v ∧ (Sum.inl u : P.Vertex) ∈ W}
  let T : Set V := {v | ¬∃ t : P.Token, P.ownedAt t v ∧ (Sum.inr t : P.Vertex) ∈ W}
  have force (z : P.Vertex) (few : (retainedNeighborComponents P.graph W z).ncard ≤ 2) : z ∈ W := by
    by_contra miss
    exact (not_lt_of_ge few) (blocked z miss)
  have stub (u : P.Stub) : (Sum.inl u : P.Vertex) ∈ W ↔ u.1 ∉ S := by
    constructor
    · exact fun yes no => no ⟨u,rfl,yes⟩
    · intro existsStub
      obtain ⟨w,hw,hk⟩ := Classical.not_not.mp existsStub
      exact force _ (P.stub_retained_with_local_stub_le_two W u w hw hk)
  have token (t : P.Token) (v : V) (own : P.ownedAt t v) : (Sum.inr t : P.Vertex) ∈ W ↔ v ∉ T := by
    constructor
    · exact fun yes no => no ⟨t,own,yes⟩
    · intro existsToken
      obtain ⟨w,hw,hk⟩ := Classical.not_not.mp existsToken
      exact force _ (P.token_retained_with_local_token_le_two W t w v own hw hk)
  have dis : Disjoint S T := by
    apply Set.disjoint_left.mpr
    intro v hs ht
    let u : P.Stub := ⟨v,.inr ⟨0,P.padding_pos v⟩⟩
    have few := P.stub_retained_no_token_le_one W u (fun t own used => ht ⟨t,own,used⟩)
    exact hs ⟨u,rfl,force _ (by omega)⟩
  have canonical : W = P.canonicalKept S T := by
    ext z
    rw [P.mem_canonicalKept]
    rcases z with u | ((a | b) | i)
    · exact stub u
    · exact token _ a.1 rfl
    · exact token _ b.1 rfl
    · exact ⟨fun _ => trivial,fun _ => force _ ((P.global_retained_le_one W i).trans (by decide))⟩
  exact ⟨S,T,dis,fun U => (best U).trans_eq (congrArg (retainedScore P.graph) canonical)⟩

#print axioms Spec.canonical_max_score
end JSP452Audit.Padded
