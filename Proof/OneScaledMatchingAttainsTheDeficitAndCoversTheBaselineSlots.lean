import ARealMaximumSlotMatchingKeepsEveryRequiredRoot
namespace JSP452Audit.StarHost
open SimpleGraph
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C]

theorem unmatched_cores_pay_hall_deficit (L:R→C→Prop) (M:(portIncidenceGraph L).Subgraph) (hm:M.IsMatching) :
    classDeficiency L Set.univ≤((PortMatching.cores M)ᶜ:Set C).ncard := by
  classical
  obtain ⟨T,_,tight⟩ := (class_deficiency_bounds L Set.univ).2
  let B := PortMatching.cores M
  let alive := T∩B
  let send (c:alive) : rootNeighbors L T :=
    ⟨(PortMatching.mates hm ⟨c.val,c.property.2⟩).val,c.val,c.property.1,PortMatching.actual_mate_incidence hm _⟩
  have inj : Function.Injective send := by
    intro a b e
    have eq : PortMatching.mates hm ⟨a.val,a.property.2⟩=PortMatching.mates hm ⟨b.val,b.property.2⟩ :=
      Subtype.ext (congrArg (fun r:rootNeighbors L T => r.val) e)
    exact Subtype.ext (congrArg (fun z:PortMatching.cores M => z.val) ((PortMatching.mates hm).injective eq))
  have enough : alive.ncard≤(rootNeighbors L T).ncard := Nat.card_le_card_of_injective send inj
  have size := Set.ncard_sdiff_add_ncard_of_subset (show alive⊆T from Set.inter_subset_left)
  have left : T\alive⊆Bᶜ := fun _ m b => m.2 ⟨m.1,b⟩
  have spare := Set.ncard_le_ncard left
  change classDeficiency L Set.univ≤(Bᶜ:Set C).ncard
  omega

def requiredRootSlots (A:Set R) (w:R→ℕ) (k:ℕ) : Set (RootSlots w) := {v|v.1∈A ∧ v.2.val<k}

theorem scaled_optimal_assignment (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (A:Set R)
    (seed:↥A↪C) (legal:∀r,L r.val (seed r)) :
    let relation := slotIncidence L w k
    let d := scaledCoreDeficit L w k Set.univ
    ∃M:(portIncidenceGraph relation).Subgraph, M.IsMatching ∧ M.edgeSet.ncard=matchingEdges (portIncidenceGraph relation) ∧
      requiredRootSlots A w k⊆PortMatching.roots M ∧ ((PortMatching.cores M)ᶜ:Set (CoreSlots C k)).ncard=d := by
  intro relation d
  let S := requiredRootSlots A w k
  let send (a:↥S) : CoreSlots C k := (seed ⟨a.val.1,a.property.1⟩,⟨a.val.2.val,a.property.2⟩)
  have inj : Function.Injective send := by
    intro a b eq
    have fst : seed ⟨a.val.1,a.property.1⟩=seed ⟨b.val.1,b.property.1⟩ := congrArg Prod.fst eq
    have first : a.val.1=b.val.1 := congrArg Subtype.val (seed.injective fst)
    have second : a.val.2.val=b.val.2.val := congrArg (fun z:CoreSlots C k => z.2.val) eq
    apply Subtype.ext
    rcases a with ⟨⟨r,s⟩,a⟩;rcases b with ⟨⟨r',t⟩,b⟩
    change r=r' at first
    subst r'
    exact congrArg (fun z:Fin (w r) => (⟨r,z⟩:RootSlots w)) (Fin.ext second)
  obtain ⟨M,hm,opt,covered,less⟩ := optimal_incidence_assignment_with_required_roots relation S ⟨send,inj⟩
    (fun a => legal ⟨a.val.1,a.property.1⟩)
  have lower := unmatched_cores_pay_hall_deficit relation M hm
  have full : fullCoreSlots (Set.univ:Set C) k=Set.univ := by ext z;simp [fullCoreSlots]
  change _≤classDeficiency relation Set.univ at less
  refine ⟨M,hm,opt,covered,?_⟩
  change _=classDeficiency relation (fullCoreSlots Set.univ k)
  rw [full];exact Nat.le_antisymm less lower

#print axioms unmatched_cores_pay_hall_deficit
#print axioms scaled_optimal_assignment
end JSP452Audit.StarHost
