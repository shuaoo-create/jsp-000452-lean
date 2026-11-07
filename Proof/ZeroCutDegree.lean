import ZeroCutMatching
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

omit [Finite X] in
theorem induced_degree_intersection (Q : SimpleGraph X) (V : Set X) (x : V) :
    Nat.card ((Q.induce V).neighborSet x)=(Q.neighborSet x.val∩V).ncard := by
  have image : Subtype.val '' ((Q.induce V).neighborSet x)=Q.neighborSet x.val∩V := by
    ext y
    exact ⟨fun ⟨a,ha,eq⟩ => eq ▸ ⟨ha,a.property⟩,fun h => ⟨⟨y,h.2⟩,h.1,rfl⟩⟩
  rw [←image,Set.ncard_image_of_injective _ Subtype.val_injective,Nat.card_coe_set_eq]

theorem degree_loss_for_named_deletion (Q : SimpleGraph X) (U K : Set X) (x : ↥(Uᶜ))
    (deleted : K⊆U) (neighbors : K⊆Q.neighborSet x.val) :
    Nat.card ((Q.induce Uᶜ).neighborSet x)+K.ncard≤Nat.card (Q.neighborSet x.val) := by
  rw [induced_degree_intersection,Nat.card_coe_set_eq]
  have dis : Disjoint (Q.neighborSet x.val∩Uᶜ) K :=
    Set.disjoint_left.mpr (fun _ h k => h.2 (deleted k))
  rw [←Set.ncard_union_eq dis]
  exact Set.ncard_le_ncard (Set.union_subset Set.inter_subset_left neighbors)

def selectedZeroCut (W : Set X) (a b i z₀ : X) : Set X :=
  (W \ {a,b})∪{i,z₀}

/-- Removing all holes except a,b and inserting one I-label and one
clique label uses exactly |W| deletions. -/
theorem selected_cut_card (W : Set X) {a b i z₀ : X} (ha : a∈W) (hb : b∈W) (ab : a≠b)
    (iw : i∉W) (zw : z₀∉W) (iz : i≠z₀) : (selectedZeroCut W a b i z₀).ncard=W.ncard := by
  have sub : ({a,b} : Set X)⊆W := by rintro x (eq|eq);exact eq ▸ ha;exact (Set.mem_singleton_iff.mp eq) ▸ hb
  have dis : Disjoint (W \ {a,b}) ({i,z₀} : Set X) := by
    apply Set.disjoint_left.mpr
    rintro x h (eq|eq)
    · exact iw (eq ▸ h.1)
    · exact zw ((Set.mem_singleton_iff.mp eq) ▸ h.1)
  have floor := Set.ncard_le_ncard sub
  rw [Set.ncard_pair ab] at floor
  simp only [selectedZeroCut,Set.ncard_union_eq dis,Set.ncard_sdiff sub,Set.ncard_pair iz,Set.ncard_pair ab]
  omega

/-- Selected root-load counts bound the degree on the actual induced
uncut labels of any surviving root. -/
theorem root_degree_selected_cut (Q : SimpleGraph X) (I W Z : Set X) (ind : Q.IsIndepSet I)
    (cover : I∪W∪Z=Set.univ) (i : I) (a b : W) (z₀ : Z) (D : ℕ)
    (bound : ∀j:I,j≠i → ({u:Z|Q.Adj j.val u.val} \ {z₀}).ncard+
      ({w:W|Q.Adj j.val w.val}∩{a,b}).ncard≤D-2) :
    let U := selectedZeroCut W a.val b.val i.val z₀.val
    ∀x : ↥(Uᶜ),x.val∈I → Nat.card ((Q.induce Uᶜ).neighborSet x)≤D-2 := by
  intro U x hi
  let j : I := ⟨x.val,hi⟩
  have ji : j≠i := fun eq => x.property (Or.inr (Or.inl (congrArg Subtype.val eq)))
  let ZN := {u:Z|Q.Adj j.val u.val} \ {z₀}
  let WN := {w:W|Q.Adj j.val w.val} ∩ {a,b}
  have sub : Q.neighborSet x.val∩Uᶜ ⊆ (Subtype.val '' ZN)∪(Subtype.val '' WN) := by
    intro y h
    have mem : y∈I∪W∪Z := cover ▸ Set.mem_univ _
    rcases mem with (yi|yw)|yz
    · exact (ind hi yi (show Q.Adj x.val y from h.1).ne h.1).elim
    · let k : W := ⟨y,yw⟩
      have pair : y∈({a.val,b.val} : Set X) := by
        by_contra hp;exact h.2 (Or.inl ⟨yw,hp⟩)
      have kp : k∈({a,b} : Set W) := by
        rcases pair with eq|eq
        · exact Or.inl (Subtype.ext eq)
        · exact Or.inr (Subtype.ext (Set.mem_singleton_iff.mp eq))
      exact Or.inr ⟨k,⟨h.1,kp⟩,rfl⟩
    · let k : Z := ⟨y,yz⟩
      have outside : k∉({z₀} : Set Z) := fun eq => h.2 (Or.inr (Or.inr
        (congrArg Subtype.val (Set.mem_singleton_iff.mp eq))))
      exact Or.inl ⟨k,⟨h.1,outside⟩,rfl⟩
  have cap := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le (Subtype.val '' ZN) (Subtype.val '' WN))
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_image_of_injective _ Subtype.val_injective] at cap
  rw [induced_degree_intersection]
  exact cap.trans (bound j ji)

#print axioms root_degree_selected_cut
end JSP452Audit.StarHost
