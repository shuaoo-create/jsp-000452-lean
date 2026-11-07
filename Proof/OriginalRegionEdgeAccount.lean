import ShorterHeadProfileBound
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Exact accounting after separating roots, full core and exterior, in the
original host. The exterior is allowed to have any number of extra edges. -/
theorem ordinary_region_original_edge_account (G : SimpleGraph X) (D : ℕ)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (K : DegreeRegion G D) :
    2*G.edgeSet.ncard+rootShortfall G K.roots D =
      2*D*(K.roots.ncard+matchingEdges (G.induce K.core))+D*minimumExposure G D+
        crossCount G K.roots K.rest+2*(G.induce K.rest).edgeSet.ncard := by
  obtain ⟨cover,apart,separate⟩ := core_rest_partition G K.barrier K.pieces
  let e := regionSumIso G K.rootsᶜ K.core K.rest cover apart (fun _ hp _ hb => separate hp hb)
  have split : (G.induce K.rootsᶜ).edgeSet.ncard=(G.induce K.core).edgeSet.ncard+(G.induce K.rest).edgeSet.ncard := by
    rw [←edge_ncard_sumGraph];exact (Nat.card_congr e.mapEdgeSet).symm
  have fee := root_deletion_cost_with_slack G K.roots D (fun v _ => cap v)
  change G.edgeSet.ncard+rootShortfall G K.roots D+(G.induce K.roots).edgeSet.ncard=
    (G.induce K.rootsᶜ).edgeSet.ncard+D*K.roots.ncard at fee
  rw [split] at fee
  have weight := K.weight_identity cap
  unfold edgeSurplus at weight
  have doubled : 2*(G.induce K.core).edgeSet.ncard =
      2*(D*matchingEdges (G.induce K.core))+D*minimumExposure G D+
        rootShortfall G K.roots D+2*(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest := by
    have eq : 2*((G.induce K.core).edgeSet.ncard:ℤ) =
        2*((D:ℤ)*(matchingEdges (G.induce K.core):ℤ))+(D:ℤ)*(minimumExposure G D:ℤ)+
          (rootShortfall G K.roots D:ℤ)+2*((G.induce K.roots).edgeSet.ncard:ℤ)+(crossCount G K.roots K.rest:ℤ) := by omega
    exact_mod_cast eq
  rw [Nat.mul_add,show 2*D*K.roots.ncard=2*(D*K.roots.ncard) by rw [Nat.mul_assoc],
    show 2*D*matchingEdges (G.induce K.core)=2*(D*matchingEdges (G.induce K.core)) by rw [Nat.mul_assoc]]
  omega

theorem ordinary_region_edge_floor (G : SimpleGraph X) (D : ℕ)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (K : DegreeRegion G D) :
    2*D*(K.roots.ncard+matchingEdges (G.induce K.core))+D*minimumExposure G D+
      2*matchingEdges (G.induce K.rest)≤2*G.edgeSet.ncard+D*K.roots.ncard := by
  have original := ordinary_region_original_edge_account G D cap K
  have root : rootShortfall G K.roots D≤D*K.roots.ncard := Nat.sub_le _ _
  have rest := matchingEdges_le_edgeCount (G.induce K.rest)
  omega

theorem nontrivial_core_count_le_region_pieces (G : SimpleGraph X) (D : ℕ) (K : DegreeRegion G D) :
    nontrivialCoreCount (G.induce K.core)≤K.roots.ncard+minimumExposure G D := by
  let H := G.induce K.core
  obtain ⟨V,size,_⟩ := critical_core_active_labels H (ordinary_core_components_critical G K)
  have bound := Set.ncard_le_ncard (Set.subset_univ V)
  rw [Set.ncard_univ,Nat.card_coe_set_eq,K.core_order] at bound
  change V.ncard=2*matchingEdges (G.induce K.core)+nontrivialCoreCount (G.induce K.core) at size
  omega

#print axioms ordinary_region_original_edge_account
#print axioms ordinary_region_edge_floor
#print axioms nontrivial_core_count_le_region_pieces
end JSP452Audit.StarHost
