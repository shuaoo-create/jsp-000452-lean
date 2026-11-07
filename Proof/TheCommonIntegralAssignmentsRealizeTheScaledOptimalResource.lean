import ExactUnassignedCoreTotalAndTrueRootLoadsAcrossTheLayers
namespace JSP452Audit.StarHost
open SimpleGraph
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C]

theorem ActualAssignmentLayers.load_required {L:R→C→Prop} {w:R→ℕ} {k:ℕ}
    {M:(portIncidenceGraph (slotIncidence L w k)).Subgraph} {hm:M.IsMatching} {A:Set R}
    (B:ActualAssignmentLayers hm A) (t:Fin k) (r:R) (must:r∈A) :
    1≤B.loadAt t r ∧ (w r=k → B.loadAt t r=1) := by
  let P:Set (PortMatching.cores M) := {i|B.colour i=t ∧ (PortMatching.mates hm i).val.1=r}
  obtain ⟨z,used,root,small⟩ := B.required r must t
  have mem:z∈P := ⟨used,root⟩
  have full : P.Nonempty := ⟨z,mem⟩
  change 1≤P.ncard ∧ (w r=k → P.ncard=1)
  refine ⟨(Set.ncard_pos (Set.toFinite _)).mpr full,?_⟩
  intro exact
  have unique : P={z} := by
    ext i
    constructor
    · intro p
      have atRoot := p.2
      have enough := (PortMatching.mates hm i).val.2.isLt
      have bound : w (PortMatching.mates hm i).val.1=k := (congrArg w atRoot).trans exact
      have below := enough.trans_eq bound
      exact B.baseUnique i z (p.1.trans used.symm) below small (atRoot.trans root.symm)
    · rintro rfl;exact mem
  rw [unique,Set.ncard_singleton]

theorem exists_layered_scaled_assignment (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (live:0<k)
    (A:Set R) (base:∀r∈A,k≤w r) (seed:↥A↪C) (legal:∀r,L r.val (seed r)) :
    let relation := slotIncidence L w k
    ∃(M:(portIncidenceGraph relation).Subgraph) (hm:M.IsMatching) (B:ActualAssignmentLayers hm A),
      (∑t:Fin k,((B.assigned t)ᶜ:Set C).ncard)=scaledCoreDeficit L w k Set.univ ∧
      (∀r,(∑t:Fin k,B.loadAt t r)≤w r) ∧
      (∀r∈A,∀t,1≤B.loadAt t r ∧ (w r=k → B.loadAt t r=1)) := by
  intro relation
  obtain ⟨M,hm,_,cover,tight⟩ := scaled_optimal_assignment L w k A seed legal
  obtain ⟨B⟩ := layer_the_same_slot_matching live M hm A base cover
  exact ⟨M,hm,B,B.total_missing.trans tight,B.root_load_total,fun r must t => B.load_required t r must⟩

#print axioms ActualAssignmentLayers.load_required
#print axioms exists_layered_scaled_assignment
end JSP452Audit.StarHost
