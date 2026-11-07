import TheWeightedWitnessUsesTheOriginalPortsAndTheExactHostRank
namespace JSP452Audit.StarHost
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C]

/-- All chosen cores can be assigned to different real slots or to d distinct
dummy slots, where d is the exact maximum Hall deficit of this same relation. -/
theorem all_cores_with_dummy_slots (L:R→C→Prop) (H:Set C) :
    let d := classDeficiency L H
    ∃f:↥H ↪ (R⊕Fin d),∀c a,f c=Sum.inl a → L a c.val := by
  classical
  intro d
  let _ := Fintype.ofFinite H
  let _ := Fintype.ofFinite R
  let allowed (c:↥H) : R⊕Fin d→Prop := Sum.elim (fun a => L a c.val) (fun _ => True)
  let nbr (c:↥H) := Finset.univ.filter (allowed c)
  have hall (T:Finset ↥H) : T.card≤(T.biUnion nbr).card := by
    by_cases empty:T=∅
    · simp [empty]
    obtain ⟨c,ct⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    let A:Set C := Subtype.val '' (T:Set ↥H)
    let N := rootNeighbors L A
    have sub:A⊆H := by rintro _ ⟨v,_,rfl⟩;exact v.property
    have cost := (class_deficiency_bounds L H).1 A sub
    have sz : A.ncard=T.card := (Set.ncard_image_of_injective _ Subtype.val_injective).trans (Set.ncard_coe_finset T)
    have real (a:↥N) : (Sum.inl a.val:R⊕Fin d)∈T.biUnion nbr := by
      obtain ⟨x,⟨v,mem,rfl⟩,hit⟩ := a.property
      exact Finset.mem_biUnion.mpr ⟨v,mem,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩⟩
    have fake (i:Fin d) : (Sum.inr i:R⊕Fin d)∈T.biUnion nbr :=
      Finset.mem_biUnion.mpr ⟨c,ct,Finset.mem_filter.mpr ⟨Finset.mem_univ _,trivial⟩⟩
    let send : ↥N⊕Fin d → ↥(T.biUnion nbr) :=
      Sum.elim (fun a => ⟨Sum.inl a.val,real a⟩) (fun i => ⟨Sum.inr i,fake i⟩)
    have inj : Function.Injective send := by
      rintro (a|a) (b|b) e
      · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val e)))
      · have clash : (Sum.inl a.val:R⊕Fin d)=Sum.inr b := congrArg Subtype.val e
        cases clash
      · have clash : (Sum.inr a:R⊕Fin d)=Sum.inl b.val := congrArg Subtype.val e
        cases clash
      · exact congrArg Sum.inr (Sum.inr.inj (congrArg Subtype.val e))
    have fee := Nat.card_le_card_of_injective send inj
    rw [Nat.card_sum,Nat.card_fin,Nat.card_coe_set_eq, Nat.card_eq_fintype_card,Fintype.card_coe] at fee
    change A.ncard≤N.ncard+d at cost
    omega
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  refine ⟨⟨f,inj⟩,?_⟩
  intro c a eq
  have ok := (Finset.mem_filter.mp (mem c)).2
  change f c=Sum.inl a at eq
  rw [eq] at ok;exact ok

#print axioms all_cores_with_dummy_slots
end JSP452Audit.StarHost
