import OddRepairGeometry
import SimultaneousCutRepair
import RepairCutCosts
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

abbrev chosenComponents {G : SimpleGraph X} {S : Set X} {D : ℕ} {A : RootAllocation G S}
    (plan : BadPortPlan G S D A) : ↥plan.chosen ↪ (G.induce Sᶜ).ConnectedComponent :=
    (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)

/-- Repair the bad-port edges before adjoining the protected good-region
vertices. This interface retains the original allocation and the same pick. -/
theorem base_port_repair_on_labels (G : SimpleGraph X) (S : Set X) (tight : IsTightBarrier G S)
    (data : ∀c : (G.induce Sᶜ).ConnectedComponent,Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (pos : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (A : RootAllocation G S) (opt : (freeFull G S D A).ncard=minimumExposure G D)
    (plan : BadPortPlan G S D A) (M : G.Subgraph) (hm : M.IsMatching) (maxM : M.edgeSet.ncard=matchingEdges G)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent,c.supp)
    (labels : exposedFull G M D=(fun c => (pick c).val.val) '' freeFull G S D A)
    (roots : ∀r:S, M.Adj r.val (pick (A.place r)).val.val)
    (yy zz : (i : ↥plan.chosen) → i.val.val.supp)
    (ay : ∀i,G.Adj (plan.root i).val (yy i).val.val)
    (oldYZ : ∀i,M.Adj (yy i).val.val (zz i).val.val)
    (noEdge : ∀i,¬G.Adj (pick i.val.val).val.val (zz i).val.val)
    (distinct : ∀i,pick i.val.val≠zz i) :
    let I := augmentedPortLabels G S D A pick (chosenComponents plan) plan.root
      (fun i => pick (A.place (plan.root i))) zz
    G.IsIndepSet I ∧ (∀x∈I,Nat.card (G.neighborSet x)=D) ∧
      I.ncard=minimumExposure G D+2*plan.chosen.ncard ∧
      matchingEdges G≤matchingEdges (G.induce Iᶜ)+plan.chosen.ncard ∧ deletionBudget (G.induce Iᶜ) D=0 := by
  classical
  let J := ↥plan.chosen
  let cf : J ↪ (G.induce Sᶜ).ConnectedComponent :=
    (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  let bb (i : J) := pick (A.place (plan.root i))
  let a : J ↪ X := plan.root.trans (Function.Embedding.subtype _)
  let b (i : J) := (bb i).val.val
  let z (i : J) := (zz i).val.val
  let y : J ↪ X := {
    toFun i := (yy i).val.val
    inj' := by
      intro i j eq
      have same : (yy i).val = (yy j).val := Subtype.ext eq
      exact cf.injective (ConnectedComponent.eq_of_common_vertex (yy i).property (same ▸ (yy j).property)) }
  have free (i : J) : cf i ∈ freeFull G S D A := i.val.property.1
  have allFull (i : J) : allFullComponent G S D (A.place (plan.root i)) :=
    incident_free_full_place_full G S tight data D A opt _ _ (free i)
      (badPortIncidence_rootIncidence G S D _ _ (plan.edge i))
  let I := augmentedPortLabels G S D A pick cf plan.root bb zz
  obtain ⟨ind,size,full⟩ := augmented_port_labels G S D A pick cf plan.root bb zz free
    (fun i eq => distinct i (Subtype.ext (Subtype.ext eq))) noEdge allFull
  have exposed : exposedFull G M D ⊆ I := by
    intro x hx
    exact Or.inl (Or.inl (labels ▸ hx))
  have bin (i : J) : b i ∈ I := Or.inl (Or.inr ⟨i,rfl⟩)
  have zin (i : J) : z i ∈ I := Or.inr ⟨i,rfl⟩
  have ab (i : J) : M.Adj (a i) (b i) := roots (plan.root i)
  have yz (i : J) : M.Adj (y i) (z i) := oldYZ i
  have outside {x t : X} (edge : M.Adj x t) (ht : t∈I) : x∉I :=
    fun hx => ind hx ht (M.adj_sub edge).ne (M.adj_sub edge)
  have dis : Disjoint (Set.range a) (Set.range y) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,same⟩
    have rootIn : a i ∈ S := (plan.root i).property
    have portIn : y j ∈ S := same.symm ▸ rootIn
    exact (yy j).val.property portIn
  have cut : M.verts ∩ I ⊆ Set.range b ∪ Set.range z := by
    rintro x ⟨matched,(hole|bLabel)|zLabel⟩
    · have missed : x ∈ exposedFull G M D := labels.symm ▸ hole
      exact (missed.1 matched).elim
    · exact Or.inl bLabel
    · exact Or.inr zLabel
  obtain ⟨N,hn,support⟩ := simultaneous_cut_repair G M hm I a y b z dis ab yz ay bin zin
    (fun i => outside (ab i) (bin i)) (fun i => outside (yz i) (zin i)) cut
  obtain ⟨rank,top⟩ := repair_cut_costs G D pos cap M hm maxM I exposed N hn
    (fun x => (support x).mpr) (Nat.card J) (ncard_le_twice_of_subset_two_ranges _ b z cut)
  exact ⟨ind,full,size.trans (congrArg (· + 2*Nat.card J) opt),rank,top⟩
#print axioms base_port_repair_on_labels
end JSP452Audit.StarHost
