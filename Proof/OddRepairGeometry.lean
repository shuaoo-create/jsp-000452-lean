import DetailedBadMatching
import IndependentAugmentedLabels
import OddGoodFullCovered
import FreePortRootMateFull

namespace JSP452Audit.StarHost
open SimpleGraph
universe u v

/-- A single original matching, independent deleted set, and named old/new
edges ready for simultaneous repair of the surviving matching. -/
structure OddRepairInputs {X : Type u} [Finite X] (G : SimpleGraph X) (D : ℕ) (J : Type v) where
  M : G.Subgraph
  I : Set X
  a : J ↪ X
  y : J ↪ X
  b : J → X
  z : J → X
  matching : M.IsMatching
  maximum : M.edgeSet.ncard = matchingEdges G
  enough : deletionBudget G D ≤ Nat.card J
  size : I.ncard = minimumExposure G D + 2*Nat.card J
  independent : G.IsIndepSet I
  full : ∀ x∈I, Nat.card (G.neighborSet x)=D
  disjoint : Disjoint (Set.range a) (Set.range y)
  oldAB : ∀ i, M.Adj (a i) (b i)
  oldYZ : ∀ i, M.Adj (y i) (z i)
  newAY : ∀ i, G.Adj (a i) (y i)
  exposed : exposedFull G M D ⊆ I
  b_mem : ∀ i, b i∈I
  z_mem : ∀ i, z i∈I
  a_out : ∀ i, a i∉I
  y_out : ∀ i, y i∉I
  used : M.verts ∩ I ⊆ Set.range b ∪ Set.range z

/-- Build the data on exactly the labels selected by the given regularized
allocation, once its chosen count meets the deletion budget. -/
theorem repair_inputs_of_port_plan {X : Type u} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph)
    (D : ℕ) (A : RootAllocation G S) (opt : (freeFull G S D A).ncard = minimumExposure G D)
    (plan : BadPortPlan G S D A) (enough : deletionBudget G D ≤ plan.chosen.ncard) :
    Nonempty (OddRepairInputs G D ↥plan.chosen) := by
  classical
  obtain ⟨M,pick,hm,maxM,_,_,labels,roots,ports⟩ := detailed_bad_port_matching G S tight data D A opt plan
  choose yy zz localLow ay pickNe oldYZ missing noEdge distinct using ports
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
  exact ⟨{ M := M, I := I, a := a, y := y, b := b, z := z,
           matching := hm, maximum := maxM, enough := by simpa only [Nat.card_coe_set_eq] using enough,
           size := size.trans (congrArg (· + 2*Nat.card J) opt), independent := ind, full := full,
           disjoint := dis, oldAB := ab, oldYZ := yz, newAY := ay,
           exposed := exposed, b_mem := bin, z_mem := zin,
           a_out := fun i => outside (ab i) (bin i), y_out := fun i => outside (yz i) (zin i),
           used := cut }⟩

/-- Odd maximum-degree parameter guarantees an actual selection of at least
κ_D original bad components, together with all simultaneous repair data. -/
theorem exists_odd_repair_inputs {X : Type u} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (odd : Odd D) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) :
    ∃ (J : Type u) (_ : Finite J), Nonempty (OddRepairInputs G D J) := by
  have parity := Nat.odd_iff.mp odd
  obtain ⟨S,A,T,tight,data,sub,opt,att,⟨plan⟩⟩ :=
    exists_optimized_disjoint_ports G D (by omega) cap
  have zero := odd_goodFull_saturated G S D odd cap (fun c => (data c).2) A T sub att
  have enough := plan.enough
  rw [zero,Nat.sub_zero] at enough
  exact ⟨↥plan.chosen,inferInstance,repair_inputs_of_port_plan G S tight data D A opt plan enough⟩

#print axioms repair_inputs_of_port_plan
#print axioms exists_odd_repair_inputs
end JSP452Audit.StarHost
