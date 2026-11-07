import BinaryTightPricing
import DegreeTwoSplit
import TightComponentSizes
import ComponentZeroReserve
namespace JSP452Audit.StarHost
open SimpleGraph
/-- All nonisolated components of a degree-two host missing the binary cost
come from this finite list. The ambient labeling is preserved by the isomorphisms. -/
theorem binary_strict_component_options {X : Type*} [Finite X] (G : SimpleGraph X)
    (p q a b : ℕ) (hp : 0<p) (hq : 0<q)
    (force : Forces G (forest (binaryProfile p a)) (forest (binaryProfile q b)))
    (cap : ∀ v, Nat.card (G.neighborSet v)≤2)
    (under : G.edgeSet.ncard < 3*(p+q-1)+2*max a b+min a b) (c : G.ConnectedComponent) :
    let k := Nat.card c.supp
    ((k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=6) ∧ Nonempty (pathGraph k ≃g c.toSimpleGraph)) ∨
      ((k=3 ∨ k=4 ∨ k=5 ∨ k=7) ∧ Nonempty (cycleGraph k ≃g c.toSimpleGraph)) := by
  intro k
  have zero := (strict_binary_tight G p q a b hp hq force (canSplitRank_of_degree_le_two G cap) under).2.2.2.2
  have tight := baseReserve_zero_components G 2 zero c
  have nonempty : Nonempty c.supp := c.nonempty_supp.to_subtype
  have pos : 0<k := Nat.card_pos
  rcases degree_two_component_classification G cap c with path | cyc
  · obtain ⟨e⟩ := path
    refine Or.inl ⟨?_,⟨e⟩⟩
    by_cases one : k=1
    · exact Or.inl one
    · exact Or.inr (tight_path_sizes k (by omega) ((baseReserve_iso e 2).trans tight))
  · obtain ⟨large,⟨e⟩⟩ := cyc
    exact Or.inr ⟨tight_cycle_sizes k large ((baseReserve_iso e 2).trans tight),⟨e⟩⟩

theorem binary_strict_component_rank_cap {X : Type*} [Finite X] (G : SimpleGraph X)
    (p q a b : ℕ) (hp : 0<p) (hq : 0<q)
    (force : Forces G (forest (binaryProfile p a)) (forest (binaryProfile q b)))
    (cap : ∀ v, Nat.card (G.neighborSet v)≤2)
    (under : G.edgeSet.ncard < 3*(p+q-1)+2*max a b+min a b) (c : G.ConnectedComponent) :
    matchingEdges c.toSimpleGraph≤3 := by
  rcases binary_strict_component_options G p q a b hp hq force cap under c with ⟨sizes,⟨e⟩⟩ | ⟨sizes,⟨e⟩⟩
  · rw [←rank_eq_of_graph_iso e,pathGraph_matchingEdges]
    omega
  · rw [←rank_eq_of_graph_iso e,cycleGraph_matchingEdges]
    omega
#print axioms binary_strict_component_options
#print axioms binary_strict_component_rank_cap
end JSP452Audit.StarHost