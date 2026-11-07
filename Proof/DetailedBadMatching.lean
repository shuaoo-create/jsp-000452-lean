import RealizedBadPorts

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- In a specified residual component, any uncovered label is its own
representative, by uniqueness of the connected component of that label. -/
theorem uncovered_eq_free_pick (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S)
    (M : G.Subgraph) (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (holes : M.vertsᶜ = freeHoleLabels G S A.place pick)
    (c : (G.induce Sᶜ).ConnectedComponent) (v : c.supp) (miss : v.val.val ∉ M.verts) :
    v = pick c := by
  have h : v.val.val ∈ M.vertsᶜ := miss
  rw [holes] at h
  obtain ⟨d, _, eq⟩ := h
  have same : (pick d).val = v.val := Subtype.ext eq
  have dc : d = c := ConnectedComponent.eq_of_common_vertex (pick d).property (same ▸ v.property)
  subst d
  exact Subtype.ext same.symm

/-- A cardinal optimum identifies all exposed full vertices on exactly this
choice of representatives. No replacement of the actual matching is needed. -/
theorem full_image_of_optimal_holes [Finite X] (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (A : RootAllocation G S) (M : G.Subgraph)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (holes : M.vertsᶜ = freeHoleLabels G S A.place pick)
    (count : (exposedFull G M D).ncard = (freeFull G S D A).ncard) :
    exposedFull G M D = (fun c => (pick c).val.val) '' freeFull G S D A := by
  have sub : (fun c => (pick c).val.val) '' freeFull G S D A ⊆ exposedFull G M D := by
    rintro _ ⟨c, hc, rfl⟩
    have free : (pick c).val.val ∈ freeHoleLabels G S A.place pick := ⟨c, hc.1, rfl⟩
    exact ⟨show (pick c).val.val ∈ M.vertsᶜ from holes.symm ▸ free, hc.2 (pick c)⟩
  symm
  apply Set.eq_of_subset_of_ncard_le sub
  rw [Set.ncard_image_of_injective _ (picked_original_injective G S pick), count]

/-- All local uncovered vertices, root mates and nonedges refer to the same
representative function and the same maximum matching on original vertices. -/
theorem detailed_bad_port_matching [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (A : RootAllocation G S)
    (opt : (freeFull G S D A).ncard = minimumExposure G D) (plan : BadPortPlan G S D A) :
    ∃ (M : G.Subgraph) (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp),
      M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      (exposedFull G M D).ncard = minimumExposure G D ∧
      M.vertsᶜ = freeHoleLabels G S A.place pick ∧
      exposedFull G M D = (fun c => (pick c).val.val) '' freeFull G S D A ∧
      (∀ a : S, M.Adj a.val (pick (A.place a)).val.val) ∧
      ∀ i : ↥plan.chosen, ∃ y z : i.val.val.supp, y ∈ portLow i.val.val.toSimpleGraph D ∧
        G.Adj (plan.root i).val y.val.val ∧ pick i.val.val ≠ y ∧ M.Adj y.val.val z.val.val ∧
        (pick i.val.val).val.val ∉ M.verts ∧ ¬G.Adj (pick i.val.val).val.val z.val.val ∧
        pick i.val.val ≠ z := by
  obtain ⟨M, hm, max, optM, ports, _, pick, holes, roots⟩ :=
    realize_bad_port_plan G S tight data D A opt plan
  refine ⟨M, pick, hm, max, optM, holes,
    full_image_of_optimal_holes G S D A M pick holes (optM.trans opt.symm), roots, ?_⟩
  intro i
  obtain ⟨y, v, z, low, rootAdj, ne, yz, miss, nonedge⟩ := ports i
  obtain rfl := uncovered_eq_free_pick G S A M pick holes i.val.val v miss
  refine ⟨y,z,low,rootAdj,ne,yz,miss,nonedge,?_⟩
  rintro eq
  exact miss (eq ▸ M.edge_vert yz.symm)

#print axioms uncovered_eq_free_pick
#print axioms full_image_of_optimal_holes
#print axioms detailed_bad_port_matching
end JSP452Audit.StarHost
