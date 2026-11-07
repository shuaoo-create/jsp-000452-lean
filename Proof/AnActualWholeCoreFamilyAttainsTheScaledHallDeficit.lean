import ScaleTheActualRootAndCoreIncidencesByTheCommonDenominator
namespace JSP452Audit.StarHost
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C]
noncomputable abbrev scaledCoreDeficit (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (H:Set C) :=
  classDeficiency (slotIncidence L w k) (fullCoreSlots H k)

theorem actual_scaled_hall_witness (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (live:0<k) (H:Set C) :
    let d := scaledCoreDeficit L w k H
    (∀S⊆H,k*S.ncard≤rootSlotCount (rootNeighbors L S) w+d) ∧
    ∃J⊆H,k*J.ncard=rootSlotCount (rootNeighbors L J) w+d ∧
      ∀T:Set (CoreSlots C k),T⊆fullCoreSlots J k →
      (rootNeighbors (slotIncidence L w k) T).ncard+d=T.ncard →
      (rootNeighbors (slotIncidence L w k) T=fullRootSlots (rootNeighbors L J) w → T=fullCoreSlots J k) := by
  classical
  intro d
  obtain ⟨upper,T,selected,saturated⟩ := class_deficiency_bounds (slotIncidence L w k) (fullCoreSlots H k)
  change T.ncard=(rootNeighbors (slotIncidence L w k) T).ncard+d at saturated
  have bound (S:Set C) (sub:S⊆H) : k*S.ncard≤rootSlotCount (rootNeighbors L S) w+d := by
    have keep : fullCoreSlots S k⊆fullCoreSlots H k := fun _ m => sub m
    have result := upper _ keep
    rw [count_full_core_slots,slot_neighbors_of_any_selection,core_slot_projection _ live] at result
    exact result
  let J := Prod.fst '' T
  have sub : J⊆H := by rintro _ ⟨x,hx,rfl⟩;exact selected hx
  have inside:T⊆fullCoreSlots J k := fun c m => ⟨c,m,rfl⟩
  have card := Set.ncard_le_ncard inside
  rw [count_full_core_slots] at card
  rw [slot_neighbors_of_any_selection] at saturated
  change T.ncard=rootSlotCount (rootNeighbors L J) w+d at saturated
  have ub := bound J sub
  have tight : k*J.ncard=rootSlotCount (rootNeighbors L J) w+d := by omega
  refine ⟨bound,J,sub,tight,?_⟩
  intro U uSub eq same
  apply Set.eq_of_subset_of_ncard_le uSub
  rw [same] at eq
  change rootSlotCount (rootNeighbors L J) w+d=U.ncard at eq
  rw [count_full_core_slots,tight,eq]

theorem slot_cost_disjoint {A B S:Set R} (w:R→ℕ) (apart:Disjoint A B) (inc:A∪B⊆S) :
    rootSlotCount A w+rootSlotCount B w≤rootSlotCount S w := by
  have dis : Disjoint (fullRootSlots A w) (fullRootSlots B w) := Set.disjoint_left.mpr (fun _ x y => Set.disjoint_left.mp apart x y)
  have sub : fullRootSlots A w∪fullRootSlots B w⊆fullRootSlots S w := by
    rintro x (a|b);exact inc (Or.inl a);exact inc (Or.inr b)
  change (fullRootSlots A w).ncard+(fullRootSlots B w).ncard≤_
  rw [←Set.ncard_union_eq dis];exact Set.ncard_le_ncard sub

theorem slot_cost_floor (w:R→ℕ) (k:ℕ) (base:∀r,k≤w r) (A:Set R) : k*A.ncard≤rootSlotCount A w := by
  classical
  let _ := Fintype.ofFinite A
  rw [count_full_root_slots]
  have fee := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => base (a:↥A).val)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Nat.mul_comm A.ncard k] using fee

#print axioms actual_scaled_hall_witness
#print axioms slot_cost_disjoint
#print axioms slot_cost_floor
end JSP452Audit.StarHost
