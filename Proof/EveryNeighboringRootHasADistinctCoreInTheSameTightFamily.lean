import AnActualWholeCoreFamilyAttainsTheScaledHallDeficit
namespace JSP452Audit.StarHost
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C]
def coresAtRoots (L:R→C→Prop) (J:Set C) (A:Set R) : Set C := {c|c∈J ∧ ∃a∈A,L a c}

theorem tight_slot_restricted_hall (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (live:0<k) (base:∀r,k≤w r)
    (H J:Set C) (inc:J⊆H) (tight:k*J.ncard=rootSlotCount (rootNeighbors L J) w+scaledCoreDeficit L w k H)
    (A:Set R) (roots:A⊆rootNeighbors L J) : A.ncard≤(coresAtRoots L J A).ncard := by
  let B := coresAtRoots L J A
  let T := J\B
  let N := rootNeighbors L T
  have sub : T⊆H := Set.sdiff_subset.trans inc
  have count := (actual_scaled_hall_witness L w k live H).1 T sub
  change k*T.ncard≤rootSlotCount N w+scaledCoreDeficit L w k H at count
  have apart : Disjoint A N := Set.disjoint_left.mpr (by
    rintro r ar ⟨c,ct,related⟩
    exact ct.2 ⟨ct.1,r,ar,related⟩)
  have bound := slot_cost_disjoint w apart (show A∪N⊆rootNeighbors L J by
    rintro r (ar|⟨c,ct,related⟩);exact roots ar;exact ⟨c,ct.1,related⟩)
  have floor := slot_cost_floor w k base A
  have incl:B⊆J := fun _ b => b.1
  have size := Set.ncard_sdiff_add_ncard_of_subset incl
  change T.ncard+B.ncard=J.ncard at size
  have scaled := congrArg (fun n => k*n) size
  change k*(T.ncard+B.ncard)=k*J.ncard at scaled
  rw [Nat.mul_add] at scaled
  have use : k*A.ncard≤k*B.ncard := by omega
  exact Nat.le_of_mul_le_mul_left use live

theorem tight_slot_actual_root_matching (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (live:0<k) (base:∀r,k≤w r)
    (H J:Set C) (inc:J⊆H) (tight:k*J.ncard=rootSlotCount (rootNeighbors L J) w+scaledCoreDeficit L w k H) :
    ∃f:↥(rootNeighbors L J) ↪ ↥J,∀r,L r.val (f r).val := by
  classical
  let A := rootNeighbors L J
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite J
  let nbr (r:↥A) := Finset.univ.filter (fun c:↥J => L r.val c.val)
  have hall (T:Finset ↥A) : T.card≤(T.biUnion nbr).card := by
    let U:Set R := Subtype.val '' (T:Set ↥A)
    have ur : U⊆A := by rintro _ ⟨x,_,rfl⟩;exact x.property
    have sizeU : U.ncard=T.card := (Set.ncard_image_of_injective _ Subtype.val_injective).trans (Set.ncard_coe_finset _)
    have reach : coresAtRoots L J U=Subtype.val '' ((T.biUnion nbr:Set ↥J)) := by
      ext c;constructor
      · rintro ⟨cj,r,⟨a,atT,rfl⟩,adj⟩
        exact ⟨⟨c,cj⟩,Finset.mem_biUnion.mpr ⟨a,atT,Finset.mem_filter.mpr ⟨Finset.mem_univ _,adj⟩⟩,rfl⟩
      · rintro ⟨c,reachable,rfl⟩
        obtain ⟨a,atT,step⟩ := Finset.mem_biUnion.mp reachable
        exact ⟨c.property,a.val,⟨a,atT,rfl⟩,(Finset.mem_filter.mp step).2⟩
    have paid := tight_slot_restricted_hall L w k live base H J inc tight U ur
    rwa [sizeU,reach,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset] at paid
  obtain ⟨f,inj,ok⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  exact ⟨⟨f,inj⟩,fun r => (Finset.mem_filter.mp (ok r)).2⟩

#print axioms tight_slot_restricted_hall
#print axioms tight_slot_actual_root_matching
end JSP452Audit.StarHost
