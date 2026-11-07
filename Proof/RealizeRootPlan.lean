import InternalNearMatching
import RootEdges
import RootPlanCounts

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Combine all internal pairs with the selected root-to-component edges.
The free representative of each unassigned component, and only those
representatives, remain uncovered in a genuine maximum matching of G. -/
theorem realize_root_plan (G : SimpleGraph X) (S : Set X) (tight : IsTightBarrier G S)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp))
    (crit : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (place : S ↪ (G.induce Sᶜ).ConnectedComponent)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (link : ∀ a : S, G.Adj a.val (pick (place a)).val.val) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      M.vertsᶜ = freeHoleLabels G S place pick := by
  classical
  let Y := G.induce Sᶜ
  let label (c : Y.ConnectedComponent) := (pick c).val.val
  have labelInj : Function.Injective label := pick_label_injective G S pick
  obtain ⟨P,hP,internals⟩ := internal_matching_away_from_picks G S crit pick
  obtain ⟨K,hK,roots⟩ := exists_root_edges_matching G S place pick link
  have internal (v : X) : v ∈ P.verts ↔ v ∉ S ∧ v ∉ Set.range label := by
    constructor
    · intro hv
      obtain ⟨c,x,rfl,diff⟩ := (internals v).mp hv
      refine ⟨x.val.property,?_⟩
      rintro ⟨d,eq⟩
      have same : (pick d).val = x.val := Subtype.ext eq
      have cd : d = c := ConnectedComponent.eq_of_common_vertex (pick d).property (same ▸ x.property)
      subst d
      exact diff (Subtype.ext same.symm)
    · rintro ⟨outside,notPick⟩
      let w : ↥(Sᶜ : Set X) := ⟨v,outside⟩
      let c := Y.connectedComponentMk w
      let x : c.supp := ⟨w,rfl⟩
      refine (internals v).mpr ⟨c,x,rfl,?_⟩
      intro hit
      exact notPick ⟨c,congrArg (fun t : c.supp => t.val.val) hit.symm⟩
  have dis : Disjoint P.verts K.verts := by
    apply Set.disjoint_left.mpr
    intro v p k
    obtain ⟨out,np⟩ := (internal v).mp p
    rcases (roots v).mp k with h | ⟨a,eq⟩
    · exact out h
    · exact np ⟨place a,eq⟩
  have matching := Padded.matching_sup_of_disjoint_verts G hP hK dis
  have holes : (P ⊔ K).vertsᶜ = freeHoleLabels G S place pick := by
    ext v
    constructor
    · intro miss
      change v ∉ P.verts ∪ K.verts at miss
      have outside : v ∉ S := fun h => miss (Or.inr ((roots v).mpr (Or.inl h)))
      have chosen : v ∈ Set.range label := by
        by_contra no
        exact miss (Or.inl ((internal v).mpr ⟨outside,no⟩))
      obtain ⟨c,eq⟩ := chosen
      refine ⟨c,?_,eq⟩
      rintro ⟨a,rfl⟩
      exact miss (Or.inr ((roots v).mpr (Or.inr ⟨a,eq⟩)))
    · rintro ⟨c,free,rfl⟩ used
      rcases used with p | k
      · exact ((internal _).mp p).2 ⟨c,rfl⟩
      · rcases (roots _).mp k with hs | ⟨a,eq⟩
        · exact (pick c).val.property hs
        · exact free ⟨a,labelInj eq⟩
  exact ⟨_,matching,maximum_of_freeHoleLabels G S place pick tight odd _ matching holes,holes⟩

#print axioms realize_root_plan
end JSP452Audit.StarHost
