import ActualCoreLayersAndTheTightDualFamilyBelongToTheSameSource
namespace JSP452Audit.StarHost.ScaledPortPlan
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D} (P:ScaledPortPlan K k c)
abbrev oldExteriorRoots := {a:↥K.barrier|a.val∉K.roots}
abbrev portLabels (t:Fin k) := ↥(P.layers.ids t)⊕↥(oldExteriorRoots (K:=K))
abbrev component (t:Fin k) (i:P.portLabels t) : (G.induce K.barrierᶜ).ConnectedComponent :=
  i.elim (fun e => e.val.val.1.val) (fun r => P.original.place r.val)
noncomputable abbrev parent (t:Fin k) (i:P.portLabels t) : X :=
  i.elim (fun e => (PortMatching.mates P.proper e.val).val.1) (fun r => r.val.val)

theorem port_incidence (t:Fin k) (i:P.portLabels t) :
    originalPortIncidence G K.barrier (P.parent t i) (P.component t i) := by
  rcases i with e|r
  · exact PortMatching.actual_mate_incidence P.proper e.val
  · exact ⟨r.val.property,P.original.link r.val⟩

theorem new_parents_inside (t:Fin k) (e:↥(P.layers.ids t)) : P.parent t (.inl e)∈K.roots := by
  have real := P.port_incidence t (.inl e)
  have hit : P.parent t (.inl e)∈rootNeighbors (originalPortIncidence G K.barrier) K.pieces :=
    ⟨_,e.val.val.1.property,real⟩
  rwa [neighboring_roots_are_original_labels] at hit

theorem component_injective (t:Fin k) : Function.Injective (P.component t) := by
  rintro (e|a) (f|b) eq
  · have base : e.val.val.1=f.val.val.1 := Subtype.ext eq
    exact congrArg Sum.inl (Subtype.ext (P.layers.coreUnique e.val f.val (e.property.trans f.property.symm) base))
  · change e.val.val.1.val=P.original.place b.val at eq
    have mixed : P.original.place b.val∈K.pieces := eq ▸ e.val.val.1.property
    exact (b.property ((P.originalInside b.val).mp mixed)).elim
  · change P.original.place a.val=f.val.val.1.val at eq
    have mixed : P.original.place a.val∈K.pieces := eq.symm ▸ f.val.val.1.property
    exact (a.property ((P.originalInside a.val).mp mixed)).elim
  · exact congrArg Sum.inr (Subtype.ext (P.original.place.injective eq))

theorem free_full_cores_in_one_layer (t:Fin k) :
    {Q| Q∉Set.range (P.component t) ∧ allFullComponent G K.barrier D Q}=
      Subtype.val '' ((P.layers.assigned t)ᶜ:Set K.pieces) := by
  ext Q;constructor
  · rintro ⟨free,full⟩
    have inside:Q∈K.pieces := by
      by_contra outside
      have unused:Q∉Set.range P.original.place := by
        rintro ⟨a,rfl⟩
        have old : a.val∉K.roots := fun used => outside ((P.originalInside a).mpr used)
        exact free ⟨.inr ⟨a,old⟩,rfl⟩
      have mem : Q∈freeFull G K.barrier D P.original := ⟨unused,full⟩
      rw [←P.originalMisses] at mem;exact outside mem.1
    refine ⟨⟨Q,inside⟩,?_,rfl⟩
    rintro ⟨e,used,eq⟩
    exact free ⟨.inl ⟨e,used⟩,congrArg Subtype.val eq⟩
  · rintro ⟨Q,free,rfl⟩
    refine ⟨?_,K.full Q.property⟩
    rintro ⟨e,eq⟩
    rcases e with e|r
    · exact free ⟨e.val,e.property,Subtype.ext eq⟩
    · change P.original.place r.val=Q.val at eq
      have mem : P.original.place r.val∈K.pieces := eq.symm ▸ Q.property
      exact r.property ((P.originalInside r.val).mp mem)

#print axioms port_incidence
#print axioms new_parents_inside
#print axioms component_injective
#print axioms free_full_cores_in_one_layer
end JSP452Audit.StarHost.ScaledPortPlan
