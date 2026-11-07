import HallNeighborhoods

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} (G : SimpleGraph X) (S : Set X)
  (T : Set (G.induce Sᶜ).ConnectedComponent)

/-- Original labels of the roots adjacent to a component of T. -/
def regionRoots : Set X := Subtype.val '' rootNeighbors (rootIncidence G S) T

/-- Original labels of precisely the vertices of the chosen components. -/
def regionCore : Set X :=
  {x | ∃ z : ↥(Sᶜ : Set X), z.val = x ∧ (G.induce Sᶜ).connectedComponentMk z ∈ T}

def regionRest : Set X := (regionRoots G S T ∪ regionCore G S T)ᶜ

theorem region_partition :
    Disjoint (regionRoots G S T) (regionCore G S T) ∧
    Disjoint (regionRoots G S T) (regionRest G S T) ∧
    Disjoint (regionCore G S T) (regionRest G S T) ∧
    regionRoots G S T ∪ regionCore G S T ∪ regionRest G S T = Set.univ := by
  refine ⟨Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_,?_⟩
  · rintro _ ⟨r,_,rfl⟩ ⟨z,eq,_⟩
    exact z.property (eq.symm ▸ r.property)
  · intro x root rest
    exact rest (Or.inl root)
  · intro x core rest
    exact rest (Or.inr core)
  · exact Set.union_compl_self _

/-- Any original neighbor of a core vertex is either an adjacent root
or lies in the very same selected residual component. -/
theorem regionCore_neighbor {x y : X} (inside : x ∈ regionCore G S T) (edge : G.Adj x y) :
    y ∈ regionRoots G S T ∪ regionCore G S T := by
  rcases inside with ⟨z,rfl,hT⟩
  let C := (G.induce Sᶜ).connectedComponentMk z
  by_cases hy : y ∈ S
  · apply Or.inl
    let a : S := ⟨y,hy⟩
    have inc : rootIncidence G S a C := ⟨⟨z,rfl⟩,edge.symm⟩
    exact ⟨a,⟨C,hT,inc⟩,rfl⟩
  · apply Or.inr
    let w : ↥(Sᶜ : Set X) := ⟨y,hy⟩
    have adj : (G.induce Sᶜ).Adj z w := edge
    have eq : (G.induce Sᶜ).connectedComponentMk z = (G.induce Sᶜ).connectedComponentMk w :=
      ConnectedComponent.sound adj.reachable
    exact ⟨w,rfl,eq ▸ hT⟩

theorem no_edge_core_rest {x y : X} (inside : x ∈ regionCore G S T)
    (outside : y ∈ regionRest G S T) : ¬ G.Adj x y :=
  fun edge => outside (regionCore_neighbor G S T inside edge)

theorem regionCore_full_degree (D : ℕ)
    (full : ∀ c ∈ T, allFullComponent G S D c) {x : X} (inside : x ∈ regionCore G S T) :
    Nat.card (G.neighborSet x) = D := by
  rcases inside with ⟨z,rfl,hT⟩
  exact full _ hT ⟨z,rfl⟩

#print axioms region_partition
#print axioms no_edge_core_rest
#print axioms regionCore_full_degree
end JSP452Audit.StarHost
