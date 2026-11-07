import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X}

/-- Both available incidences at an interior path vertex are already used by
the path, so every original neighbor is one of its path neighbors. -/
theorem degree_two_internal_neighbors (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2)
    {a b : X} {p : G.Walk a b} (hp : p.IsPath) {x : X} (hx : x ∈ p.support)
    (ha : x ≠ a) (hb : x ≠ b) : p.toSubgraph.neighborSet x = G.neighborSet x := by
  obtain ⟨i,hi,le⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  have left : i ≠ 0 := fun eq => ha (hi.symm.trans (eq ▸ p.getVert_zero))
  have ne : i ≠ p.length := fun eq => hb (hi.symm.trans (eq ▸ p.getVert_length))
  have n := hp.ncard_neighborSet_toSubgraph_internal_eq_two left (lt_of_le_of_ne le ne)
  rw [hi] at n
  exact Set.eq_of_subset_of_ncard_le (fun _ h => p.toSubgraph.adj_sub h) ((cap x).trans_eq n.symm)

/-- A genuine longest path of a connected graph of maximum degree two spans
all original vertices, including the one-vertex graph. -/
theorem degree_two_longest_path_spans (conn : G.Connected)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) {a b : X} {p : G.Walk a b} (hp : p.IsPath)
    (longest : ∀ (u v : X) (q : G.Walk u v), q.IsPath → q.length ≤ p.length) :
    ∀ x, x ∈ p.support := by
  have closed {x y : X} (inside : x ∈ p.support) (edge : G.Adj x y) : y ∈ p.support := by
    by_contra out
    by_cases left : x = a
    · subst x
      have h := longest y b (.cons edge.symm p) (hp.cons out)
      simp at h
    by_cases right : x = b
    · subst x
      have h := longest a y (p.concat edge) (hp.concat out edge)
      simp at h
    have eq := degree_two_internal_neighbors cap hp inside left right
    have pathEdge : p.toSubgraph.Adj x y := by
      change y ∈ p.toSubgraph.neighborSet x
      rw [eq]
      exact edge
    exact out (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert pathEdge.symm))
  intro x
  have reach := (reachable_iff_reflTransGen a x).mp (conn.preconnected a x)
  induction reach with
  | refl => exact p.start_mem_support
  | tail _ e ih => exact closed ih e

/-- Once a simple path spans, only its two ends can be joined by any remaining
host edge absent from the path. -/
theorem degree_two_extra_edge_ends (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2)
    {a b : X} {p : G.Walk a b} (hp : p.IsPath) (spans : ∀ x, x ∈ p.support)
    {x y : X} (h : G.Adj x y) (absent : ¬p.toSubgraph.Adj x y) :
    (x=a ∧ y=b) ∨ (x=b ∧ y=a) := by
  have endpoint {u v : X} (e : G.Adj u v) (no : ¬p.toSubgraph.Adj u v) : u = a ∨ u = b := by
    by_contra! both
    have eq := degree_two_internal_neighbors cap hp (spans u) both.1 both.2
    exact no (show v ∈ p.toSubgraph.neighborSet u by rw [eq]; exact e)
  have xend := endpoint h absent
  have yend := endpoint h.symm (fun e => absent e.symm)
  have ne := h.ne
  grind


/-- A spanning copy whose every vertex has already used all two available
neighbors cannot have extra host edges. -/
private theorem iso_at_two {I : Type*} [Finite I] {C : SimpleGraph I}
    (f : C.Copy G) (same : Nat.card I = Nat.card X)
    (full : ∀ x, Nat.card (C.neighborSet x) = 2)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) : Nonempty (C ≃g G) := by
  let e := Equiv.ofBijective f (f.injective.bijective_of_nat_card_le same.ge)
  have neighbors (x : I) : f '' C.neighborSet x = G.neighborSet (f x) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro _ ⟨y,edge,rfl⟩
      exact f.toHom.map_adj edge
    · rw [Set.ncard_image_of_injective (f := (⇑f : I → X)) _ (show Function.Injective (⇑f : I → X) from f.injective)]
      exact (cap _).trans_eq (full x).symm
  refine ⟨⟨e,?_⟩⟩
  intro x y
  constructor
  · intro h
    have hx : f y ∈ G.neighborSet (f x) := h
    rw [← neighbors] at hx
    obtain ⟨z,hz,eq⟩ := hx
    exact f.injective eq ▸ hz
  · exact f.toHom.map_adj

/-- An exact classification with the graph's true order, and a nondegenerate
cycle in the second alternative. The one-vertex case is included in the path. -/
theorem degree_two_connected_classification (G : SimpleGraph X) (conn : G.Connected)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) :
    Nonempty (pathGraph (Nat.card X) ≃g G) ∨
      (3 ≤ Nat.card X ∧ Nonempty (cycleGraph (Nat.card X) ≃g G)) := by
  classical
  let _ := conn.nonempty
  let _ := Fintype.ofFinite X
  obtain ⟨a,b,p,hp,longest⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have spans := degree_two_longest_path_spans conn cap hp longest
  have allVerts : p.toSubgraph.IsSpanning := fun x => p.mem_verts_toSubgraph.mpr (spans x)
  let pathIso := hp.pathGraphIsoToSubgraph.trans (p.toSubgraph.spanningCoeEquivCoeOfSpanning allVerts).symm
  have card : p.length+1 = Nat.card X := by simpa only [Nat.card_fin] using Nat.card_congr pathIso.toEquiv
  rw [← card]
  by_cases allEdges : ∀ x y, G.Adj x y → p.toSubgraph.Adj x y
  · left
    have eq : p.toSubgraph.spanningCoe = G := by
      ext x y; exact ⟨p.toSubgraph.adj_sub,allEdges x y⟩
    exact (congrArg (fun H : SimpleGraph X => Nonempty (pathGraph (p.length+1) ≃g H)) eq).mp ⟨pathIso⟩
  · right
    push Not at allEdges
    obtain ⟨x,y,edge,absent⟩ := allEdges
    have closing : G.Adj b a ∧ ¬p.toSubgraph.Adj b a := by
      rcases degree_two_extra_edge_ends cap hp spans edge absent with h | h
      · obtain ⟨rfl,rfl⟩ := h
        exact ⟨edge.symm,fun back => absent back.symm⟩
      · obtain ⟨rfl,rfl⟩ := h
        exact ⟨edge,absent⟩
    let cycle := Walk.cons closing.1 p
    have hc : cycle.IsCycle := (Walk.cons_isCycle_iff p closing.1).mpr
      ⟨hp,fun member => closing.2 (p.adj_toSubgraph_iff_mem_edges.mpr member)⟩
    have len : cycle.length = p.length+1 := rfl
    have large : 3 ≤ p.length+1 := len ▸ hc.isCircuit.three_le_length
    refine ⟨large,?_⟩
    obtain ⟨f⟩ := (cycleGraph_isContained_iff large).mpr ⟨b,cycle,hc,len⟩
    apply iso_at_two f (by simpa only [Nat.card_fin] using card) _ cap
    have evaluate (n : ℕ) (hn : 3 ≤ n) : ∀ x, Nat.card ((cycleGraph n).neighborSet x) = 2 := by
      obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [Nat.add_comm 3 m]
      intro x
      rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,cycleGraph_degree_three_le]
    exact evaluate _ large


/-- Apply the classification to each genuine component, including singleton
components, even when the original graph itself is disconnected. -/
theorem degree_two_component_classification (G : SimpleGraph X)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) (c : G.ConnectedComponent) :
    Nonempty (pathGraph (Nat.card c.supp) ≃g c.toSimpleGraph) ∨
      (3 ≤ Nat.card c.supp ∧ Nonempty (cycleGraph (Nat.card c.supp) ≃g c.toSimpleGraph)) := by
  apply degree_two_connected_classification c.toSimpleGraph c.connected_toSimpleGraph
  intro x
  let incl (y : c.toSimpleGraph.neighborSet x) : G.neighborSet x.val := ⟨y.val.val,y.property⟩
  have inj : Function.Injective incl := fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun y : G.neighborSet x.val => y.val) h))
  exact (Nat.card_le_card_of_injective incl inj).trans (cap x.val)

#print axioms degree_two_component_classification

#print axioms degree_two_connected_classification

#print axioms degree_two_longest_path_spans
#print axioms degree_two_extra_edge_ends
end JSP452Audit.StarHost
