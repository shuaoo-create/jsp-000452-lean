import OddDegreePeakExposureAndTheTwoElevenDegreeCuts
namespace JSP452Audit.StarHost
universe u v
variable {R:Type u} {C:Type v}

abbrev RootSlots (w:R→ℕ) := Σa:R,Fin (w a)
abbrev CoreSlots (C:Type v) (k:ℕ) := C×Fin k
def slotIncidence (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (a:RootSlots w) (c:CoreSlots C k) : Prop := L a.1 c.1
def fullCoreSlots (T:Set C) (k:ℕ) : Set (CoreSlots C k) := {c|c.1∈T}
def fullRootSlots (A:Set R) (w:R→ℕ) : Set (RootSlots w) := {a|a.1∈A}
noncomputable abbrev rootSlotCount (A:Set R) (w:R→ℕ) := (fullRootSlots A w).ncard

theorem count_full_core_slots (T:Set C) (k:ℕ) : (fullCoreSlots T k).ncard=k*T.ncard := by
  let e : ↥(fullCoreSlots T k) ≃ (↥T×Fin k) := {
    toFun := fun c => (⟨c.val.1,c.property⟩,c.val.2)
    invFun := fun c => ⟨(c.1.val,c.2),c.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl}
  have count := Nat.card_congr e
  rw [Nat.card_prod,Nat.card_fin] at count
  change Nat.card ↥(fullCoreSlots T k)=k*Nat.card ↥T
  exact count.trans (Nat.mul_comm _ _)

theorem count_full_root_slots (A:Set R) (w:R→ℕ) [Fintype A] : rootSlotCount A w=∑a:↥A,w a.val := by
  let e : ↥(fullRootSlots A w) ≃ (Σa:↥A,Fin (w a.val)) := {
    toFun := fun a => ⟨⟨a.val.1,a.property⟩,a.val.2⟩
    invFun := fun a => ⟨⟨a.1.val,a.2⟩,a.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl}
  have count := Nat.card_congr e
  rw [Nat.card_sigma] at count
  change (fullRootSlots A w).ncard=∑a:↥A,w a.val
  rw [←Nat.card_coe_set_eq]
  simpa only [Nat.card_fin] using count

theorem slot_neighbors_of_any_selection (L:R→C→Prop) (w:R→ℕ) (k:ℕ) (T:Set (CoreSlots C k)) :
    rootNeighbors (slotIncidence L w k) T=fullRootSlots (rootNeighbors L (Prod.fst '' T)) w := by
  ext a;constructor
  · rintro ⟨c,hc,e⟩
    exact ⟨c.1,⟨c,hc,rfl⟩,e⟩
  · rintro ⟨c,⟨b,hb,rfl⟩,e⟩
    exact ⟨b,hb,e⟩

theorem core_slot_projection (T:Set C) {k:ℕ} (live:0<k) : Prod.fst '' fullCoreSlots T k=T := by
  ext c;constructor
  · rintro ⟨b,hb,rfl⟩;exact hb
  · intro mem;exact ⟨(c,⟨0,live⟩),mem,rfl⟩

#print axioms count_full_core_slots
#print axioms count_full_root_slots
#print axioms slot_neighbors_of_any_selection
#print axioms core_slot_projection
end JSP452Audit.StarHost
