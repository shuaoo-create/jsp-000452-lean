import CoverDegreeSplit

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- A vertex of full host degree that has no partner in this matching. -/
def exposedFull (G : SimpleGraph X) (M : G.Subgraph) (D : ℕ) : Set X :=
  {v | v ∉ M.verts ∧ Nat.card (G.neighborSet v) = D}

/-- Pull back the original matched vertices and their actual pairs, with original labels. -/
def matchingOffExposed (G : SimpleGraph X) (M : G.Subgraph) (D : ℕ) :
    (G.induce (exposedFull G M D)ᶜ).Subgraph where
  verts := {x | x.val ∈ M.verts}
  Adj x y := M.Adj x.val y.val
  adj_sub := fun h => M.adj_sub h
  edge_vert := fun h => M.edge_vert h
  symm := ⟨fun _ _ h => h.symm⟩

theorem matchingOffExposed_isMatching (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    (D : ℕ) : (matchingOffExposed G M D).IsMatching := by
  intro x hx
  obtain ⟨y,edge,uniq⟩ := hM hx
  have hy : y ∉ exposedFull G M D := fun bad => bad.1 (M.edge_vert edge.symm)
  exact ⟨⟨y,hy⟩,edge,fun z hz => Subtype.ext (uniq z.val hz)⟩

/-- Inclusion of genuine neighbors does not increase a degree under induction. -/
theorem induced_neighbor_count_le [Finite X] (G : SimpleGraph X) (S : Set X) (x : S) :
    Nat.card ((G.induce S).neighborSet x) ≤ Nat.card (G.neighborSet x.val) := by
  let incl (y : (G.induce S).neighborSet x) : G.neighborSet x.val := ⟨y.val.val,y.property⟩
  have inj : Function.Injective incl := fun _ _ he =>
    Subtype.ext (Subtype.ext (congrArg (fun y : G.neighborSet x.val => y.val) he))
  exact Nat.card_le_card_of_injective incl inj

/-- A surviving vertex still of full degree in the induced graph has an actual surviving mate. -/
theorem exposed_compl_cover [Finite X] (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    (D : ℕ) (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D) :
    let Y := G.induce (exposedFull G M D)ᶜ
    ∃ N : Y.Subgraph, N.IsMatching ∧ ∀ x, Nat.card (Y.neighborSet x) = D → x ∈ N.verts := by
  refine ⟨matchingOffExposed G M D,matchingOffExposed_isMatching G M hM D,?_⟩
  intro x deg
  have eq : Nat.card (G.neighborSet x.val) = D :=
    le_antisymm (bound _) (deg.ge.trans (induced_neighbor_count_le G _ x))
  change x.val ∈ M.verts
  by_contra miss
  exact x.property ⟨miss,eq⟩

theorem degree_split_off_exposed [Finite X] (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    (p q : ℕ) (bound : ∀ v, Nat.card (G.neighborSet v) ≤ p+q) :
    let Y := G.induce (exposedFull G M (p+q))ᶜ
    ∃ R, R ≤ Y ∧ ∀ v, Nat.card (R.neighborSet v) ≤ p ∧ Nat.card ((Y \ R).neighborSet v) ≤ q := by
  apply degree_split_from_cover _ p q
  · intro x
    exact (induced_neighbor_count_le G _ x).trans (bound x.val)
  · exact exposed_compl_cover G M hM (p+q) bound

#print axioms matchingOffExposed_isMatching
#print axioms induced_neighbor_count_le
#print axioms exposed_compl_cover
#print axioms degree_split_off_exposed
end JSP452Audit.StarHost
