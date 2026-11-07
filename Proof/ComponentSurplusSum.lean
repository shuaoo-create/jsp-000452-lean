import RegionWeights
import BudgetCeiling

namespace JSP452Audit.StarHost
open SimpleGraph

theorem edgeSurplus_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (D : ℕ) :
    edgeSurplus G D = edgeSurplus H D := by
  have edges : G.edgeSet.ncard = H.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  simp only [edgeSurplus,edges,rank_eq_of_graph_iso e]

theorem edgeSurplus_sumGraph {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (D : ℕ) :
    edgeSurplus (G ⊕g H) D = edgeSurplus G D + edgeSurplus H D := by
  simp only [edgeSurplus,edge_ncard_sumGraph,matchingEdges_sumGraph,Nat.cast_add,mul_add]
  omega

private def selectedVertices {X : Type*} (Y : SimpleGraph X) (T : Finset Y.ConnectedComponent) :
    Set X := {x | Y.connectedComponentMk x ∈ T}

/-- A finite union of whole original components has exactly the sum of
their signed surpluses. Components with negative surplus are retained. -/
theorem surplus_component_finset {X : Type*} [Finite X] (Y : SimpleGraph X)
    (T : Finset Y.ConnectedComponent) (D : ℕ) :
    edgeSurplus (Y.induce {x | Y.connectedComponentMk x ∈ T}) D =
      ∑ c ∈ T, edgeSurplus (Y.induce c.supp) D := by
  classical
  change edgeSurplus (Y.induce (selectedVertices Y T)) D = _
  induction T using Finset.induction_on with
  | empty =>
      have empty : Y.induce (selectedVertices Y ∅) = ⊥ := by
        ext x
        exact False.elim (Finset.notMem_empty _ x.property)
      simp [empty,edgeSurplus,matchingEdges_bot]
  | @insert c t fresh ih =>
      have cover : c.supp ∪ selectedVertices Y t = selectedVertices Y (insert c t) := by
        ext x
        change (_ ∨ _) ↔ Y.connectedComponentMk x ∈ insert c t
        exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (selectedVertices Y t) := by
        apply Set.disjoint_left.mpr
        intro x xc xt
        have eq : Y.connectedComponentMk x = c := xc
        exact fresh (eq ▸ xt)
      have sep : ∀ x ∈ c.supp, ∀ y ∈ selectedVertices Y t, ¬Y.Adj x y :=
        fun _ xc _ yt edge => Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp xc) yt
      let iso := regionSumIso Y (selectedVertices Y (insert c t)) c.supp (selectedVertices Y t)
        cover apart sep
      rw [← edgeSurplus_iso iso D, edgeSurplus_sumGraph, ih, Finset.sum_insert fresh]

private def originalCoreIso {X : Type*} (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    G.induce (regionCore G S T) ≃g (G.induce Sᶜ).induce {z | (G.induce Sᶜ).connectedComponentMk z ∈ T} := by
  let f (x : regionCore G S T) : {z // (G.induce Sᶜ).connectedComponentMk z ∈ T} := by
    have out : x.val ∈ Sᶜ := by obtain ⟨z,h,_⟩ := x.property; exact h ▸ z.property
    refine ⟨⟨x.val,out⟩,?_⟩
    obtain ⟨z,h,mem⟩ := x.property
    have same : (⟨x.val,out⟩ : ↥(Sᶜ : Set X)) = z := Subtype.ext h.symm
    rwa [same]
  let g (z : {z // (G.induce Sᶜ).connectedComponentMk z ∈ T}) : regionCore G S T :=
    ⟨z.val.val,⟨z.val,rfl,z.property⟩⟩
  exact { toEquiv := ⟨f,g,fun _ => rfl,fun _ => rfl⟩, map_rel_iff' := Iff.rfl }

theorem core_surplus_eq_sum {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) [Fintype T] (D : ℕ) :
    edgeSurplus (G.induce (regionCore G S T)) D =
      ∑ c : T, edgeSurplus ((G.induce Sᶜ).induce c.val.supp) D := by
  classical
  let Y := G.induce Sᶜ
  let t := T.toFinite.toFinset
  have remains : {x | Y.connectedComponentMk x ∈ T} = selectedVertices Y t := by
    ext x
    exact (Set.Finite.mem_toFinset T.toFinite).symm
  rw [edgeSurplus_iso (originalCoreIso G S T) D]
  change edgeSurplus (Y.induce {x | Y.connectedComponentMk x ∈ T}) D = _
  rw [remains]
  change edgeSurplus (Y.induce {x | Y.connectedComponentMk x ∈ t}) D = _
  rw [surplus_component_finset]
  symm
  apply Finset.sum_bij (fun (c : T) _ => c.val)
  · intro c _
    exact (Set.Finite.mem_toFinset _).mpr c.property
  · intro _ _ _ _ eq
    exact Subtype.ext eq
  · intro c mem
    exact ⟨⟨c,(Set.Finite.mem_toFinset _).mp mem⟩,Finset.mem_univ _,rfl⟩
  · intro _ _
    rfl

#print axioms surplus_component_finset
#print axioms core_surplus_eq_sum
end JSP452Audit.StarHost
