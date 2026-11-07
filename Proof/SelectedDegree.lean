import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- The graph on X retaining exactly the specified genuine (unoriented) edges. -/
def selectedGraph (G : SimpleGraph X) (A : Set G.edgeSet) : SimpleGraph X :=
  fromEdgeSet (Subtype.val '' A)

theorem selectedGraph_edges (G : SimpleGraph X) (A : Set G.edgeSet) :
    (selectedGraph G A).edgeSet = Subtype.val '' A := by
  have noDiag : Disjoint (Subtype.val '' A) Sym2.diagSet :=
    Set.disjoint_left.mpr fun _ ⟨e,_,eq⟩ hd => G.edgeSet_subset_compl_diagSet e.2 (eq ▸ hd)
  exact (edgeSet_fromEdgeSet _).trans noDiag.sdiff_eq_left

theorem selectedGraph_le (G : SimpleGraph X) (A : Set G.edgeSet) : selectedGraph G A ≤ G := by
  apply edgeSet_subset_edgeSet.mp
  rw [selectedGraph_edges]
  rintro _ ⟨e,_,rfl⟩
  exact e.2

@[simp] theorem mem_selectedGraph_edges (G : SimpleGraph X) (A : Set G.edgeSet) (e : G.edgeSet) :
    e.val ∈ (selectedGraph G A).edgeSet ↔ e ∈ A := by
  rw [selectedGraph_edges]
  constructor
  · rintro ⟨d,hd,h⟩; exact (Subtype.ext h : d = e) ▸ hd
  · exact fun h => ⟨e,h,rfl⟩

@[simp] theorem selectedGraph_univ (G : SimpleGraph X) : selectedGraph G Set.univ = G := by
  apply edgeSet_inj.mp
  rw [selectedGraph_edges]
  ext e
  exact ⟨fun ⟨d,_,h⟩ => h ▸ d.2, fun h => ⟨⟨e,h⟩,Set.mem_univ _,rfl⟩⟩

/-- Count incidences by their original edge, before splitting according to orientation. -/
private def selectedIncidenceEquiv (G : SimpleGraph X) (A : Set G.edgeSet) (v : X) :
    {e : G.edgeSet // e ∈ A ∧ v ∈ e.val} ≃ (selectedGraph G A).incidenceSet v where
  toFun e := ⟨e.1.val,(mem_selectedGraph_edges G A e.1).mpr e.2.1,e.2.2⟩
  invFun e :=
    let orig : G.edgeSet := ⟨e.val,edgeSet_subset_edgeSet.mpr (selectedGraph_le G A) e.2.1⟩
    ⟨orig,(mem_selectedGraph_edges G A orig).mp e.2.1,e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An actual selected edge at v contributes exactly once: either it leaves v
or it enters v. No orientation balance assumption is needed. -/
theorem selectedGraph_degree [Finite X] (G : SimpleGraph X) (A : Set G.edgeSet)
    (src dst : G.edgeSet → X) (orient : ∀ e, s(src e,dst e) = e.val) (v : X) :
    Nat.card ((selectedGraph G A).neighborSet v) =
      Nat.card {e : G.edgeSet // e ∈ A ∧ src e = v} +
      Nat.card {e : G.edgeSet // e ∈ A ∧ dst e = v} := by
  classical
  let out : Set G.edgeSet := {e | e ∈ A ∧ src e = v}
  let incoming : Set G.edgeSet := {e | e ∈ A ∧ dst e = v}
  let incident : Set G.edgeSet := {e | e ∈ A ∧ v ∈ e.val}
  have split : incident = out ∪ incoming := by
    ext e
    change e ∈ A ∧ v ∈ e.val ↔ (e ∈ A ∧ src e = v) ∨ (e ∈ A ∧ dst e = v)
    rw [← orient e, Sym2.mem_iff]
    tauto
  have apart : Disjoint out incoming := by
    apply Set.disjoint_left.mpr
    rintro e ⟨_,hs⟩ ⟨_,ht⟩
    have pair := orient e
    rw [hs,ht] at pair
    have impossible : G.Adj v v := G.mem_edgeSet.mp (pair.symm ▸ e.2)
    exact G.irrefl impossible
  have counts := Nat.card_congr ((selectedIncidenceEquiv G A v).trans
    ((selectedGraph G A).incidenceSetEquivNeighborSet v))
  calc
    Nat.card ((selectedGraph G A).neighborSet v) = incident.ncard := counts.symm
    _ = out.ncard + incoming.ncard := by rw [split,Set.ncard_union_eq apart]
    _ = _ := rfl

/-- The neighbor counts add when two actual edge sets on the same vertex
type are disjoint. -/
theorem neighbor_card_sup_of_disjoint [Finite X] {G H : SimpleGraph X}
    (disj : Disjoint G H) (v : X) :
    Nat.card ((G ⊔ H).neighborSet v) = Nat.card (G.neighborSet v) + Nat.card (H.neighborSet v) := by
  simp only [Nat.card_coe_set_eq, neighborSet_sup, Set.ncard_union_eq (disjoint_neighborSet.mpr disj v)]

#print axioms selectedGraph_edges
#print axioms selectedGraph_le
#print axioms selectedGraph_degree
#print axioms neighbor_card_sup_of_disjoint
end JSP452Audit.StarHost
