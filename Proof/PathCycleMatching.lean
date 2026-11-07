import TutteJoin
import PairFamily
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

/-- Any graph containing the indexed spanning path attains the universal
half-order matching bound, with pairs 0–1, 2–3, and so on. -/
theorem matchingEdges_of_spanning_path (n : ℕ) (G : SimpleGraph (Fin n)) (path : pathGraph n ≤ G) :
    matchingEdges G = n/2 := by
  let even : Fin (n/2) ↪ Fin n := {
    toFun i := ⟨2*i.val,by have := i.isLt; omega⟩
    inj' := fun _ _ h => Fin.ext (by have e := congrArg (fun j : Fin n => j.val) h; dsimp at e; omega) }
  let odd : Fin (n/2) ↪ Fin n := {
    toFun i := ⟨2*i.val+1,by have := i.isLt; omega⟩
    inj' := fun _ _ h => Fin.ext (by have e := congrArg (fun j : Fin n => j.val) h; dsimp at e; omega) }
  have edge (i : Fin (n/2)) : G.Adj (even i) (odd i) := path (pathGraph_adj.mpr (Or.inl rfl))
  have apart : Disjoint (Set.range even) (Set.range odd) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,h⟩
    have e := congrArg (fun a : Fin n => a.val) h
    change 2*j.val+1 = 2*i.val at e
    omega
  let M := pairFamily G even odd edge
  have hm := pairFamily_isMatching G even odd edge apart
  have count := matching_vertices_eq_twice_edges hm
  rw [pairFamily_verts,Set.ncard_union_eq apart,Set.ncard_range_of_injective even.injective,
    Set.ncard_range_of_injective odd.injective,Nat.card_fin] at count
  have lower := le_matchingEdges hm
  obtain ⟨K,hK,hmax⟩ := exists_maximum_matching G
  have upper := Set.ncard_le_ncard K.verts.subset_univ
  rw [Set.ncard_univ,Nat.card_fin,matching_vertices_eq_twice_edges hK,hmax] at upper
  omega

theorem pathGraph_matchingEdges (n : ℕ) : matchingEdges (pathGraph n) = n/2 :=
  matchingEdges_of_spanning_path n (pathGraph n) le_rfl

theorem cycleGraph_matchingEdges (n : ℕ) : matchingEdges (cycleGraph n) = n/2 :=
  matchingEdges_of_spanning_path n (cycleGraph n) pathGraph_le_cycleGraph

#print axioms matchingEdges_of_spanning_path
#print axioms pathGraph_matchingEdges
#print axioms cycleGraph_matchingEdges
end JSP452Audit.StarHost
