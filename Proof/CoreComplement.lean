import HallRegions
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} (G : SimpleGraph X) (S : Set X)
  (T : Set (G.induce Sᶜ).ConnectedComponent)

theorem core_complement_partition :
    regionCore G S T ∪ regionCore G S Tᶜ = Sᶜ ∧
    Disjoint (regionCore G S T) (regionCore G S Tᶜ) ∧
    ∀ ⦃x y : X⦄, x ∈ regionCore G S T → y ∈ regionCore G S Tᶜ → ¬ G.Adj x y := by
  constructor
  · ext x
    constructor
    · rintro (⟨z,rfl,_⟩ | ⟨z,rfl,_⟩) <;> exact z.property
    · intro hx
      let z : ↥(Sᶜ : Set X) := ⟨x,hx⟩
      by_cases hc : (G.induce Sᶜ).connectedComponentMk z ∈ T
      · exact Or.inl ⟨z,rfl,hc⟩
      · exact Or.inr ⟨z,rfl,hc⟩
  constructor
  · apply Set.disjoint_left.mpr
    rintro x ⟨z,rfl,inside⟩ ⟨w,eq,outside⟩
    exact outside ((Subtype.ext eq : w = z).symm ▸ inside)
  · rintro _ _ ⟨z,rfl,inside⟩ ⟨w,rfl,outside⟩ edge
    have inResidual : (G.induce Sᶜ).Adj z w := edge
    exact outside (ConnectedComponent.sound inResidual.reachable ▸ inside)

theorem core_rest_partition :
    regionCore G S T ∪ regionRest G S T = (regionRoots G S T)ᶜ ∧
    Disjoint (regionCore G S T) (regionRest G S T) ∧
    ∀ ⦃x y : X⦄, x ∈ regionCore G S T → y ∈ regionRest G S T → ¬ G.Adj x y := by
  obtain ⟨rootsCore,rootsRest,coreRest,_⟩ := region_partition G S T
  refine ⟨?_,coreRest,fun _ _ hx hy => no_edge_core_rest G S T hx hy⟩
  ext x
  constructor
  · rintro (core | rest) root
    · exact Set.disjoint_left.mp rootsCore root core
    · exact Set.disjoint_left.mp rootsRest root rest
  · intro noRoot
    by_cases core : x ∈ regionCore G S T
    · exact Or.inl core
    · exact Or.inr (fun h => h.elim noRoot core)

#print axioms core_complement_partition
#print axioms core_rest_partition
end JSP452Audit.StarHost
