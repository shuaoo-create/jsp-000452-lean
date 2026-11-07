import HallRegions

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} (G : SimpleGraph X) (S : Set X) (T : Set (G.induce Sᶜ).ConnectedComponent)

private def coreInclusion : G.induce (regionCore G S T) ↪g G.induce Sᶜ where
  toFun x := ⟨x.val,by obtain ⟨z,h,_⟩ := x.property; exact h ▸ z.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun z : ↥(Sᶜ : Set X) => z.val) h)
  map_rel_iff' := Iff.rfl

private theorem inclusion_mem (x : regionCore G S T) :
    (G.induce Sᶜ).connectedComponentMk (coreInclusion G S T x) ∈ T := by
  obtain ⟨z,h,mem⟩ := x.property
  have eq : coreInclusion G S T x = z := Subtype.ext h.symm
  rwa [eq]

private def originalToCore (c : (G.induce Sᶜ).ConnectedComponent) (hc : c ∈ T) :
    c.toSimpleGraph ↪g G.induce (regionCore G S T) where
  toFun z := ⟨z.val.val,⟨z.val,rfl,((c.mem_supp_iff _).mp z.property).symm ▸ hc⟩⟩
  inj' := fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : regionCore G S T => z.val) h))
  map_rel_iff' := Iff.rfl

private def compTag (C : (G.induce (regionCore G S T)).ConnectedComponent) : ↥T :=
  ⟨C.map (coreInclusion G S T).toHom,C.ind (fun x => inclusion_mem G S T x)⟩

private theorem compTag_inj : Function.Injective (compTag G S T) := by
  intro C D
  refine ConnectedComponent.ind₂ (fun x y => ?_) C D
  intro h
  let incl := coreInclusion G S T
  let c := (G.induce Sᶜ).connectedComponentMk (incl x)
  have same : (G.induce Sᶜ).connectedComponentMk (incl y) = c :=
    (congrArg (fun z : T => z.val) h).symm
  have path := c.reachable_toSimpleGraph (u := incl x) (v := incl y) rfl same
  exact ConnectedComponent.sound (path.map (originalToCore G S T c (inclusion_mem G S T x)).toHom)

/-- Exact correspondence, retaining the original connected component tag. -/
noncomputable def coreComponentEquiv :
    (G.induce (regionCore G S T)).ConnectedComponent ≃ ↥T := by
  apply Equiv.ofBijective (compTag G S T)
  refine ⟨compTag_inj G S T,?_⟩
  rintro ⟨c,hc⟩
  let z := c.nonempty_supp.choose
  have mem := c.nonempty_supp.choose_spec
  let x := originalToCore G S T c hc ⟨z,mem⟩
  exact ⟨(G.induce (regionCore G S T)).connectedComponentMk x,Subtype.ext mem⟩

/-- The corresponding induced component graphs are isomorphic by the original
vertex label, so each order, all internal edges, and parity are preserved. -/
noncomputable def coreComponentIso (C : (G.induce (regionCore G S T)).ConnectedComponent) :
    C.toSimpleGraph ≃g ((coreComponentEquiv G S T C).val).toSimpleGraph := by
  let e := coreComponentEquiv G S T
  let f (x : C.supp) : (e C).val.supp :=
    ⟨coreInclusion G S T x.val,congrArg (fun d => (e d).val) ((C.mem_supp_iff _).mp x.property)⟩
  let g (y : (e C).val.supp) : C.supp :=
    ⟨originalToCore G S T (e C).val (e C).property y,e.injective (Subtype.ext y.property)⟩
  exact { toEquiv := ⟨f,g,fun _ => rfl,fun _ => rfl⟩
          map_rel_iff' := Iff.rfl }

theorem coreComponent_order (C : (G.induce (regionCore G S T)).ConnectedComponent) :
    C.supp.ncard = (coreComponentEquiv G S T C).val.supp.ncard :=
  Nat.card_congr (coreComponentIso G S T C).toEquiv

theorem odd_components_regionCore :
    (G.induce (regionCore G S T)).oddComponents.ncard =
      Nat.card {c : T // Odd (Nat.card c.val.supp)} := by
  let e := coreComponentEquiv G S T
  apply Nat.card_congr (e.subtypeEquiv _)
  intro c
  change Odd c.supp.ncard ↔ Odd (e c).val.supp.ncard
  rw [coreComponent_order G S T c]

theorem odd_components_regionCore_of_all_odd
    (allOdd : ∀ c ∈ T, Odd (Nat.card c.supp)) :
    (G.induce (regionCore G S T)).oddComponents.ncard = T.ncard := by
  rw [odd_components_regionCore]
  apply Nat.card_congr
  exact { toFun := Subtype.val, invFun := fun c => ⟨c,allOdd c.val c.property⟩
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }

#print axioms coreComponentEquiv
#print axioms coreComponentIso
#print axioms odd_components_regionCore_of_all_odd
end JSP452Audit.StarHost
