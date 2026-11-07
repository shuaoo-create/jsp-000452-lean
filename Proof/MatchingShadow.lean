import PaddedGraph
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace JSP452Audit.Padded
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Take exactly those original edges whose two real stubs are joined in M. -/
def Spec.redShadow (M : P.graph.Subgraph) : SimpleGraph V where
  Adj v w := ∃ e : P.G.Adj v w, M.Adj (P.realStub v w e) (P.realStub w v e.symm)
  symm := ⟨by
    rintro v w ⟨e, h⟩
    exact ⟨e.symm, h.symm⟩⟩
  loopless := ⟨by
    rintro v ⟨e, _⟩
    exact P.G.ne_of_adj e rfl⟩

theorem Spec.redShadow_le (M : P.graph.Subgraph) : P.redShadow M ≤ P.G := by
  intro v w h
  exact h.choose

theorem Spec.redShadow_adj_iff (M : P.graph.Subgraph) {v w : V} (e : P.G.Adj v w) :
    (P.redShadow M).Adj v w ↔ M.Adj (P.realStub v w e) (P.realStub w v e.symm) := by
  constructor
  · rintro ⟨_, he⟩
    exact he
  · exact fun he => ⟨e, he⟩

/-- Red neighbors are precisely the real incident stubs used across original edges. -/
def Spec.redNeighborEquiv (M : P.graph.Subgraph) (v : V) :
    (P.redShadow M).neighborSet v ≃
      {w : P.G.neighborSet v //
        M.Adj (P.realStub v w.val w.property) (P.realStub w.val v w.property.symm)} where
  toFun w := ⟨⟨w.val, P.redShadow_le M w.property⟩,
               (P.redShadow_adj_iff M (P.redShadow_le M w.property)).mp w.property⟩
  invFun w := ⟨w.val.val, (P.redShadow_adj_iff M w.val.property).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem Spec.redDegree_eq (M : P.graph.Subgraph) (v : V)
    [Fintype ((P.redShadow M).neighborSet v)]
    [Fintype {w : P.G.neighborSet v //
      M.Adj (P.realStub v w.val w.property) (P.realStub w.val v w.property.symm)}] :
    (P.redShadow M).degree v =
      Fintype.card {w : P.G.neighborSet v //
        M.Adj (P.realStub v w.val w.property) (P.realStub w.val v w.property.symm)} :=
  ((P.redShadow M).card_neighborSet_eq_degree v).symm.trans
    (Fintype.card_congr (P.redNeighborEquiv M v))

theorem Spec.cross_used_blocks_token (M : P.graph.Subgraph) (hM : M.IsMatching)
    {v w : V} (e : P.G.Adj v w) (selected : (P.redShadow M).Adj v w) (tok : P.Token) :
    ¬ M.Adj (P.realStub v w e) (.inr tok) := by
  intro localEdge
  have other := (P.redShadow_adj_iff M e).mp selected
  have impossible := hM.eq_of_adj_left other localEdge
  cases impossible

#print axioms Spec.redShadow
#print axioms Spec.redShadow_adj_iff
#print axioms Spec.redDegree_eq
#print axioms Spec.cross_used_blocks_token
end JSP452Audit.Padded
