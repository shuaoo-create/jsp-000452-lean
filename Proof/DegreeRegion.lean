import RegionHandshake
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- A single tight cut and its actual Hall-deficient set of full components.
The point, rank and edge accounts below all refer to these same sets. -/
structure DegreeRegion (G : SimpleGraph X) (D : ℕ) where
  barrier : Set X
  pieces : Set (G.induce barrierᶜ).ConnectedComponent
  tight : IsTightBarrier G barrier
  critical : ∀ c : (G.induce barrierᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
    PerfectAfterEveryDeletion ((G.induce barrierᶜ).induce c.supp)
  full : pieces ⊆ {c | allFullComponent G barrier D c}
  balanced : pieces.ncard=(rootNeighbors (rootIncidence G barrier) pieces).ncard + minimumExposure G D

theorem degreeRegion_exists (G : SimpleGraph X) (D : ℕ) : Nonempty (DegreeRegion G D) := by
  obtain ⟨S,tight,data⟩ := exists_critical_barrier G
  obtain ⟨T,full,cert⟩ := (full_component_deficiency G S tight data D).2
  exact ⟨⟨S,T,tight,data,full,cert⟩⟩

namespace DegreeRegion
variable {G : SimpleGraph X} {D : ℕ} (r : DegreeRegion G D)
abbrev roots := regionRoots G r.barrier r.pieces
abbrev core := regionCore G r.barrier r.pieces
abbrev rest := regionRest G r.barrier r.pieces

theorem core_order : r.core.ncard=2*matchingEdges (G.induce r.core)+r.roots.ncard+minimumExposure G D := by
  have rootCount : r.roots.ncard=(rootNeighbors (rootIncidence G r.barrier) r.pieces).ncard :=
    Set.ncard_image_of_injective _ Subtype.val_injective
  have eq := core_order_matching G r.barrier r.tight r.pieces (fun c _ => (r.critical c).1)
  have att := r.balanced
  change r.core.ncard = 2*matchingEdges (G.induce r.core)+r.pieces.ncard at eq
  omega

theorem weight_identity (cap : ∀ x, Nat.card (G.neighborSet x)≤D) :
    2*edgeSurplus (G.induce r.core) D = (D:ℤ)*(minimumExposure G D:ℤ) +
      (rootShortfall G r.roots D:ℤ) + 2*((G.induce r.roots).edgeSet.ncard:ℤ) + (crossCount G r.roots r.rest:ℤ) := by
  obtain ⟨ac,ab,cb,cover⟩ := region_partition G r.barrier r.pieces
  exact weight_handshake G r.roots r.core r.rest D _ (fun x _ => cap x)
    (fun _ hx => regionCore_full_degree G r.barrier r.pieces D r.full hx) ac ab cb cover
    (fun _ hx _ hy => no_edge_core_rest G r.barrier r.pieces hx hy) r.core_order
end DegreeRegion
#print axioms degreeRegion_exists
#print axioms DegreeRegion.weight_identity
end JSP452Audit.StarHost