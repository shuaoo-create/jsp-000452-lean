import FullForestOnSum
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

/-- The shifted row after deleting the actual roots and any W in the same
core. The blue suffix has more stars than the entire exterior matching rank. -/
theorem whole_forest_after_core_deletion {s t r D d : ℕ} (G : SimpleGraph X)
    (hs : 0<s) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (positive : 0<d) (account : matchingEdges G+d=rowCount s t r) (K : DegreeRegion G D)
    (trigger : s≤matchingEdges (G.induce K.core)+d) (W : Set X) (inside : W⊆K.core)
    (budget : W.ncard≤matchingEdges (G.induce K.core)+d-s) :
    (forest n).IsContained (G.induce (K.core\W)) := by
  let U := K.roots∪W
  let P := K.core\W
  obtain ⟨cover,apart,separate⟩ := core_rest_partition G K.barrier K.pieces
  change K.core∪K.rest=K.rootsᶜ at cover
  change Disjoint K.core K.rest at apart
  have out : K.core⊆K.rootsᶜ := cover ▸ Set.subset_union_left
  have dis : Disjoint K.roots W := Set.disjoint_left.mpr (fun _ root w => out (inside w) root)
  have card : U.ncard=K.roots.ncard+W.ncard := Set.ncard_union_eq dis
  have part : P∪K.rest=Uᶜ := by
    ext v
    constructor
    · rintro (⟨core,away⟩|rest) (root|w)
      · exact out core root
      · exact away w
      · exact (show v∈K.rootsᶜ from cover ▸ Or.inr rest) root
      · exact Set.disjoint_left.mp apart (inside w) rest
    · intro hv
      have noRoot : v∈K.rootsᶜ := fun root => hv (Or.inl root)
      have m : v∈K.core∪K.rest := cover.symm ▸ noRoot
      exact m.elim (fun core => Or.inl ⟨core,fun w => hv (Or.inr w)⟩) Or.inr
  have iso := regionSumIso G Uᶜ P K.rest part (apart.mono_left (fun _ h => h.1))
    (fun _ hp _ hr => separate hp.1 hr)
  have shifted := row_delete_set G U _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  have rank := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=K.roots.ncard+matchingEdges (G.induce K.core)+matchingEdges (G.induce K.rest) at rank
  have short : matchingEdges (G.induce K.rest)+(r+U.ncard)<t := by
    dsimp [rowCount] at account
    omega
  exact sum_row_forces_whole_left (G.induce P) (G.induce K.rest) hs n m pn pm
    (forcingRow_of_iso iso.symm shifted) short

/-- Both orientations of Liu's whole-list embedding use the very same
strict source, degree region, and original surviving vertex labels. -/
theorem strict_source_robust_whole_forests (F : StrictFamily.{u}) {D : ℕ} (K : DegreeRegion F.G D) :
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    (F.s≤μ+d → ∀W:Set F.X,W⊆K.core → W.ncard≤μ+d-F.s →
      (forest F.n).IsContained (F.G.induce (K.core\W))) ∧
    (F.t≤μ+d → ∀W:Set F.X,W⊆K.core → W.ncard≤μ+d-F.t →
      (forest F.m).IsContained (F.G.induce (K.core\W))) := by
  intro μ d
  have price := row_energy_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row
  have strict := F.strict
  change rowEnergy F.n F.m F.r+matchingEdges F.G≤F.G.edgeSet.ncard+F.rank at price
  have pos : 0<d := by dsimp [d];omega
  have eq : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  refine ⟨fun trigger W sub budget => whole_forest_after_core_deletion F.G F.hs F.n F.m F.hn F.hm
    F.pn F.pm F.row pos eq K trigger W sub budget,?_⟩
  have flip : matchingEdges F.G+d=rowCount F.t F.s F.r := by rwa [rowCount,Nat.add_comm F.t F.s]
  exact fun trigger W sub budget => whole_forest_after_core_deletion F.G F.ht F.m F.n F.hm F.hn
    F.pm F.pn (swap_positive_forcing_row F.G _ _ F.row) pos flip K trigger W sub budget

#print axioms whole_forest_after_core_deletion
#print axioms strict_source_robust_whole_forests
end JSP452Audit.StarHost
