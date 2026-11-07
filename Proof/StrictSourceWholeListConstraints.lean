import CoreForestMass
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

/-- For one original list in one actual region: the short side of the gap,
or a deletion-resistant embedding paying both half-order and vertex mass. -/
def WholeListRegionAlternative {s : ℕ} (G : SimpleGraph X) (A : Set X) (n : Fin s→ℕ) (d : ℕ) : Prop :=
  let H := G.induce A
  let μ := matchingEdges H
  μ+d+1≤s ∨ (s+d+2*(∑i,(n i-1)/2)≤μ+1 ∧ (∑i,n i)+d≤μ+nontrivialCoreCount H ∧
    ∀W:Set X,W⊆A → W.ncard≤μ+d-s → (forest n).IsContained (G.induce (A\W)))

private theorem whole_list_actual_alternative {s D : ℕ} (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (pn : ∀i,1≤n i) (d : ℕ) (smallD : d≤s)
    (copy : s≤matchingEdges (G.induce K.core)+d →
      ∀W:Set X,W⊆K.core → W.ncard≤matchingEdges (G.induce K.core)+d-s →
        (forest n).IsContained (G.induce (K.core\W))) : WholeListRegionAlternative G K.core n d := by
  let H := G.induce K.core
  change matchingEdges H+d+1≤s ∨ _
  by_cases active : s≤matchingEdges H+d
  · have each := copy active
    have lifted := robust_core_subtype n G K.core _ each
    have crit := ordinary_core_components_critical G K
    exact Or.inr ⟨robust_whole_half_order H n pn crit d smallD active lifted,
      robust_whole_mass H n pn crit d smallD active lifted,each⟩
  exact Or.inl (by omega)

theorem strict_source_whole_list_alternatives (F : StrictFamily.{u}) {D : ℕ} (K : DegreeRegion F.G D) :
    WholeListRegionAlternative F.G K.core F.n (F.rank-matchingEdges F.G) ∧
    WholeListRegionAlternative F.G K.core F.m (F.rank-matchingEdges F.G) := by
  obtain ⟨red,blue⟩ := strict_source_robust_whole_forests F K
  obtain ⟨ls,lt⟩ := le_min_iff.mp (strict_source_strong_lengths F).1
  exact ⟨whole_list_actual_alternative F.G K F.n F.pn _ (by omega) red,
    whole_list_actual_alternative F.G K F.m F.pm _ (by omega) blue⟩

theorem embedding_iff_length_le_region_rank {s : ℕ} (G : SimpleGraph X) (A : Set X) (n : Fin s→ℕ)
    (pn : ∀i,1≤n i) (d : ℕ) (alt : WholeListRegionAlternative G A n d) :
    (forest n).IsContained (G.induce A) ↔ s≤matchingEdges (G.induce A) := by
  constructor
  · intro copy
    have cap := forest_copy_matching (G.induce A) n pn copy
    simpa only [Fintype.card_fin] using cap
  · intro length
    rcases alt with short|⟨_,_,all⟩
    · omega
    have found := all ∅ (Set.empty_subset _) (by simp)
    have eq : A\(∅ : Set X)=A := by ext v;simp
    rwa [eq] at found

/-- The actual minimal counterexample to the full original identity must
simultaneously satisfy the deficit, both list alternatives and both
embedding equivalences for every one of its ordinary degree regions. -/
theorem original_failure_whole_list_constraints {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑k∈Finset.Icc 2 (s+t),diagonal n m k) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      let D := diagonal F.n F.m (F.r+2)-1
      let d := F.rank-matchingEdges F.G
      minimumExposure F.G D+1≤d ∧ 2≤d ∧
      ∀K:DegreeRegion F.G D,
        WholeListRegionAlternative F.G K.core F.n d ∧ WholeListRegionAlternative F.G K.core F.m d ∧
        ((forest F.n).IsContained (F.G.induce K.core) ↔ F.s≤matchingEdges (F.G.induce K.core)) ∧
        ((forest F.m).IsContained (F.G.induce K.core) ↔ F.t≤matchingEdges (F.G.induce K.core)) := by
  obtain ⟨F,paid,edges,order⟩ := failure_has_smaller_rank_baseline.{u} hs ht n m hn hm pn pm fail
  obtain ⟨_,charge,two⟩ := minimal_strict_source_deficit F paid
  exact ⟨F,paid,edges,order,charge,two,fun K => by
    obtain ⟨red,blue⟩ := strict_source_whole_list_alternatives F K
    exact ⟨red,blue,embedding_iff_length_le_region_rank F.G K.core F.n F.pn _ red,
      embedding_iff_length_le_region_rank F.G K.core F.m F.pm _ blue⟩⟩

#print axioms strict_source_whole_list_alternatives
#print axioms embedding_iff_length_le_region_rank
#print axioms original_failure_whole_list_constraints
end JSP452Audit.StarHost
