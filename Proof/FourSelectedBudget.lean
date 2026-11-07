import FourCutMates
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem selected_degree_at_root (Q : SimpleGraph X) (I W Z : Set X)
    (ind : Q.IsIndepSet I) (cover : I∪W∪Z=Set.univ)
    (i : I) (a b : W) (z₀ : Z) (x : ↥((selectedZeroCut W a.val b.val i.val z₀.val)ᶜ : Set X))
    (hi : x.val∈I) :
    Nat.card ((Q.induce (selectedZeroCut W a.val b.val i.val z₀.val)ᶜ).neighborSet x)≤
      ({u:Z|Q.Adj x.val u.val} \ {z₀}).ncard+({w:W|Q.Adj x.val w.val}∩{a,b}).ncard := by
  let U := selectedZeroCut W a.val b.val i.val z₀.val
  let j : I := ⟨x.val,hi⟩
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
  exact cap

/-- In degree four the two named root mates can cover saturated surviving
roots. The selected cut deletes exactly as many vertices as the hole set. -/
theorem four_selected_cut_budget (Q : SimpleGraph X) (I W Z : Set X)
    (reg : ∀x,Nat.card (Q.neighborSet x)=4)
    (ind : Q.IsIndepSet I) (cl : Q.IsClique Z) (iw : Disjoint I W) (iz : Disjoint I Z)
    (wz : Disjoint W Z) (cover : I∪W∪Z=Set.univ) (size : Z.ncard=4)
    (i : I) (z z₀ : Z) (a b : W) (zi : Q.Adj z.val i.val) (zz : z≠z₀)
    (ab : a≠b) (ia : Q.Adj i.val a.val) (ib : Q.Adj i.val b.val)
    (p q : I) (pi : p≠i) (qi : q≠i) (pq : p≠q) (ap : Q.Adj a.val p.val) (bq : Q.Adj b.val q.val)
    (rootLoad : ∀j:I,j≠i →
      let L := ({u:Z|Q.Adj j.val u.val} \ {z₀}).ncard+({w:W|Q.Adj j.val w.val}∩{a,b}).ncard
      L≤3 ∧ (L=3 → j=p ∨ j=q)) : deletionBudget Q 3≤W.ncard := by
  classical
  let U := selectedZeroCut W a.val b.val i.val z₀.val
  let H := Q.induce Uᶜ
  have ivz : i.val≠z₀.val := fun eq => Set.disjoint_left.mp iz i.property (eq ▸ z₀.property)
  have sameSize := selected_cut_card W a.property b.property
    (fun eq => ab (Subtype.ext eq)) (Set.disjoint_left.mp iw i.property)
    (Set.disjoint_left.mp wz.symm z₀.property) ivz
  have liveI {x : X} (hx : x∈I) (diff : x≠i.val) : x∉U := by
    rintro (hw|eq|eq)
    · exact Set.disjoint_left.mp iw hx hw.1
    · exact diff eq
    · exact Set.disjoint_left.mp iz hx ((Set.mem_singleton_iff.mp eq).symm ▸ z₀.property)
  have liveW {x : X} (hx : x∈W) (keep : x∈({a.val,b.val} : Set X)) : x∉U := by
    rintro (hw|eq|eq)
    · exact hw.2 keep
    · exact Set.disjoint_left.mp iw i.property (eq ▸ hx)
    · exact Set.disjoint_left.mp wz hx ((Set.mem_singleton_iff.mp eq).symm ▸ z₀.property)
  have liveZ {x : X} (hx : x∈Z) (diff : x≠z₀.val) : x∉U := by
    rintro (hw|eq|eq)
    · exact Set.disjoint_left.mp wz hw.1 hx
    · exact Set.disjoint_left.mp iz i.property (eq ▸ hx)
    · exact diff (Set.mem_singleton_iff.mp eq)
  let cA : ↥(Uᶜ) := ⟨a.val,liveW a.property (Or.inl rfl)⟩
  let cB : ↥(Uᶜ) := ⟨b.val,liveW b.property (Or.inr rfl)⟩
  let cP : ↥(Uᶜ) := ⟨p.val,liveI p.property (fun eq => pi (Subtype.ext eq))⟩
  let cQ : ↥(Uᶜ) := ⟨q.val,liveI q.property (fun eq => qi (Subtype.ext eq))⟩
  let V := Z \ {z.val,z₀.val}
  let C : Set ↥(Uᶜ) := {x|x.val∈V}
  have vLive (x : X) (hx : x∈V) : x∉U := liveZ hx.1 (fun eq => hx.2 (Or.inr eq))
  have image : Subtype.val '' C=V := by
    ext x;exact ⟨fun ⟨b,hb,eq⟩ => eq ▸ hb,fun hx => ⟨⟨x,vLive x hx⟩,hx,rfl⟩⟩
  have cc : H.IsClique C := by
    intro x hx y hy ne
    exact cl hx.1 hy.1 (fun eq => ne (Subtype.ext eq))
  have ce : Even C.ncard := by
    have sub : ({z.val,z₀.val} : Set X)⊆Z := by
      rintro x (eq|eq); exact eq ▸ z.property;exact (Set.mem_singleton_iff.mp eq) ▸ z₀.property
    have d : z.val≠z₀.val := fun eq => zz (Subtype.ext eq)
    rw [←Set.ncard_image_of_injective C Subtype.val_injective,image]
    change Even (Z \ {z.val,z₀.val}).ncard
    rw [Set.ncard_sdiff sub,size,Set.ncard_pair d,Nat.even_iff]
  have ac : cA∉C := fun h => Set.disjoint_left.mp wz a.property h.1
  have bc : cB∉C := fun h => Set.disjoint_left.mp wz b.property h.1
  have pc : cP∉C := fun h => Set.disjoint_left.mp iz p.property h.1
  have qc : cQ∉C := fun h => Set.disjoint_left.mp iz q.property h.1
  have out : ∀x,x∈({cA,cP,cB,cQ} : Set _) → x∉C := by
    rintro x (eq|eq|eq|eq)
    · exact eq ▸ ac
    · exact eq ▸ pc
    · exact eq ▸ bc
    · exact (Set.mem_singleton_iff.mp eq) ▸ qc
  have a_ne_b : cA≠cB := fun eq => ab (Subtype.ext (congrArg (fun v : ↥(Uᶜ) => v.val) eq))
  have a_ne_q : cA≠cQ := by
    intro eq
    have aq : a.val=q.val := congrArg (fun v : ↥(Uᶜ) => v.val) eq
    exact Set.disjoint_left.mp iw q.property (aq ▸ a.property)
  have p_ne_b : cP≠cB := by
    intro eq
    have pb : p.val=b.val := congrArg (fun v : ↥(Uᶜ) => v.val) eq
    exact Set.disjoint_left.mp iw p.property (pb.symm ▸ b.property)
  have p_ne_q : cP≠cQ := fun eq => pq (Subtype.ext (congrArg (fun v : ↥(Uᶜ) => v.val) eq))
  have sep : Disjoint ({cA,cP} : Set _) {cB,cQ} := by
    apply Set.disjoint_left.mpr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have iRemoved : i.val∈U := Or.inr (Or.inl rfl)
  have zRemoved : z₀.val∈U := Or.inr (Or.inr rfl)
  have lose {x : ↥(Uᶜ)} {y : X} (gone : y∈U) (adj : Q.Adj x.val y) :
      Nat.card (H.neighborSet x)≤3 := by
    have cut := degree_loss_for_named_deletion Q U {y} x
      (Set.singleton_subset_iff.mpr gone) (Set.singleton_subset_iff.mpr adj)
    rw [Set.ncard_singleton,reg] at cut
    change Nat.card (H.neighborSet x)+1≤4 at cut
    omega
  have bounds (x : ↥(Uᶜ)) : Nat.card (H.neighborSet x)≤3 ∧
      (Nat.card (H.neighborSet x)=3 → x∈C ∨ x∈({cA,cP,cB,cQ} : Set _)) := by
    have mem : x.val∈I∪W∪Z := cover ▸ Set.mem_univ _
    rcases mem with (hx|hx)|hx
    · let j : I := ⟨x.val,hx⟩
      have ji : j≠i := fun eq => x.property ((congrArg Subtype.val eq) ▸ iRemoved)
      have bound := selected_degree_at_root Q I W Z ind cover i a b z₀ x hx
      obtain ⟨cap,heavy⟩ := rootLoad j ji
      exact ⟨bound.trans cap,fun top => Or.inr (by
        rcases heavy (le_antisymm cap (top ▸ bound)) with ep|eq
        · exact Or.inr (Or.inl (Subtype.ext (congrArg (fun v : I => v.val) ep)))
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (congrArg (fun v : I => v.val) eq)))))⟩
    · have pair : x.val∈({a.val,b.val} : Set X) := by
        by_contra h;exact x.property (Or.inl ⟨hx,h⟩)
      rcases pair with eq|eq
      · exact ⟨lose iRemoved (eq ▸ ia.symm),fun _ => Or.inr (Or.inl (Subtype.ext eq))⟩
      · have eq' := Set.mem_singleton_iff.mp eq
        exact ⟨lose iRemoved (eq' ▸ ib.symm),fun _ => Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext eq'))))⟩
    · have nz : x.val≠z₀.val := fun eq => x.property (eq ▸ zRemoved)
      have edge := cl hx z₀.property nz
      refine ⟨lose zRemoved edge,?_⟩
      intro top
      by_cases eq : x.val=z.val
      · have subset : ({i.val,z₀.val} : Set X)⊆U := by
          rintro v (e|e);exact e ▸ iRemoved;exact (Set.mem_singleton_iff.mp e) ▸ zRemoved
        have nsub : ({i.val,z₀.val} : Set X)⊆Q.neighborSet x.val := by
          rintro v (e|e)
          · exact e ▸ (eq ▸ zi)
          · exact (Set.mem_singleton_iff.mp e) ▸ edge
        have degree := degree_loss_for_named_deletion Q U {i.val,z₀.val} x subset nsub
        rw [Set.ncard_pair ivz,reg] at degree
        change Nat.card (H.neighborSet x)+2≤4 at degree
        omega
      · exact Or.inl ⟨hx,fun h => h.elim eq (fun e => nz (Set.mem_singleton_iff.mp e))⟩
  have remainder := four_layer_remainder_with_two_full_roots H C cc ce cA cB cP cQ ap bq out sep
    (fun x => (bounds x).1) (fun x => (bounds x).2)
  exact (deletionBudget_le_of_witness Q 3 U remainder).trans_eq sameSize


#print axioms four_selected_cut_budget
end JSP452Audit.StarHost
