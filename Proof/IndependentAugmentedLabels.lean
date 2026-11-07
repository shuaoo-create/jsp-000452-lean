import RootAllocation
import RootEdges

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X J : Type*} (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp)
    (cf : J ↪ (G.induce Sᶜ).ConnectedComponent) (r : J ↪ ↥S)
    (b : ∀ i, (A.place (r i)).supp) (z : ∀ i, (cf i).supp)

/-- One exposed label per free full component, one assigned-component label
per selected root, and a further label in each selected free component. -/
def augmentedPortLabels : Set X :=
  ((fun c => (pick c).val.val) '' freeFull G S D A ∪ Set.range (fun i => (b i).val.val)) ∪
    Set.range (fun i => (z i).val.val)

private def touchesLabel (x y : X) := x=y ∨ G.Adj x y

private theorem touches_symm {x y : X} (h : touchesLabel G x y) : touchesLabel G y x :=
  h.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)

/-- Original labels outside S sharing a vertex or joined by an original edge
must come from one and the same component of the induced complement. -/
private theorem component_of_touch {c d : (G.induce Sᶜ).ConnectedComponent}
    (x : c.supp) (y : d.supp) (touch : touchesLabel G x.val.val y.val.val) : c=d := by
  have hx : (G.induce Sᶜ).connectedComponentMk x.val=c := x.property
  have hy : (G.induce Sᶜ).connectedComponentMk y.val=d := y.property
  apply hx.symm.trans
  apply Eq.trans _ hy
  rcases touch with eq|edge
  · exact congrArg _ (Subtype.ext eq)
  · exact ConnectedComponent.sound (show (G.induce Sᶜ).Adj x.val y.val from edge).reachable

theorem augmented_port_labels [Finite X] [Finite J]
    (free : ∀ i, cf i∈freeFull G S D A)
    (distinct : ∀ i, (pick (cf i)).val.val ≠ (z i).val.val)
    (nonadj : ∀ i, ¬ G.Adj (pick (cf i)).val.val (z i).val.val)
    (assignedFull : ∀ i, allFullComponent G S D (A.place (r i))) :
    let I := augmentedPortLabels G S D A pick cf r b z
    G.IsIndepSet I ∧ I.ncard=(freeFull G S D A).ncard+2*Nat.card J ∧
      ∀ x∈I, Nat.card (G.neighborSet x)=D := by
  intro I
  let F := freeFull G S D A
  let label : (↥F ⊕ (J ⊕ J)) → X :=
    Sum.elim (fun c => (pick c.val).val.val)
      (Sum.elim (fun i => (b i).val.val) (fun i => (z i).val.val))
  have freeAssigned {c : (G.induce Sᶜ).ConnectedComponent} (hc : c∈F) (x : c.supp) (i : J)
      (touch : touchesLabel G x.val.val (b i).val.val) : False :=
    hc.1 ⟨r i,(component_of_touch G S x (b i) touch).symm⟩
  have freeExtra (c : (G.induce Sᶜ).ConnectedComponent) (i : J)
      (touch : touchesLabel G (pick c).val.val (z i).val.val) : False := by
    have same := component_of_touch G S (pick c) (z i) touch
    subst c
    exact touch.elim (distinct i) (nonadj i)
  have identifies (x y : ↥F ⊕ (J ⊕ J)) (touch : touchesLabel G (label x) (label y)) : x=y := by
    rcases x with x|x <;> rcases y with y|y
    · exact congrArg Sum.inl (Subtype.ext (component_of_touch G S (pick x.val) (pick y.val) touch))
    · rcases y with j|j
      · exact (freeAssigned x.property (pick x.val) j touch).elim
      · exact (freeExtra x.val j touch).elim
    · rcases x with i|i
      · exact (freeAssigned y.property (pick y.val) i (touches_symm G touch)).elim
      · exact (freeExtra y.val i (touches_symm G touch)).elim
    · rcases x with i|i <;> rcases y with j|j
      · have same := component_of_touch G S (b i) (b j) touch
        exact congrArg Sum.inr (congrArg Sum.inl (r.injective (A.place.injective same)))
      · exact (freeAssigned (free j) (z j) i (touches_symm G touch)).elim
      · exact (freeAssigned (free i) (z i) j touch).elim
      · have same := component_of_touch G S (z i) (z j) touch
        exact congrArg Sum.inr (congrArg Sum.inr (cf.injective same))
  have range_eq : Set.range label = I := by
    ext x
    constructor
    · rintro ⟨c|j,rfl⟩
      · exact Or.inl (Or.inl ⟨c.val,c.property,rfl⟩)
      · rcases j with i|i
        · exact Or.inl (Or.inr ⟨i,rfl⟩)
        · exact Or.inr ⟨i,rfl⟩
    · rintro ((⟨c,hc,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩)
      · exact ⟨Sum.inl ⟨c,hc⟩,rfl⟩
      · exact ⟨Sum.inr (Sum.inl i),rfl⟩
      · exact ⟨Sum.inr (Sum.inr i),rfl⟩
  have inj : Function.Injective label := fun {x y} eq => identifies x y (Or.inl eq)
  refine ⟨?_,?_,?_⟩
  · rw [←range_eq]
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ ne edge
    exact ne (congrArg label (identifies i j (Or.inr edge)))
  · rw [←range_eq,Set.ncard_range_of_injective inj,Nat.card_sum,Nat.card_sum,Nat.card_coe_set_eq]
    dsimp only [F]
    omega
  · rintro _ ((⟨c,hc,rfl⟩|⟨i,rfl⟩)|⟨i,rfl⟩)
    · exact hc.2 (pick c)
    · exact assignedFull i (b i)
    · exact (free i).2 (z i)

#print axioms augmented_port_labels
end JSP452Audit.StarHost
