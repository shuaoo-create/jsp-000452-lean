import ZeroCutDegree
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem select_distinct_mates (Q : SimpleGraph X) (I : Set X) (D : ℕ) (large : 3≤D)
    (a b i : X) (deg : ∀w,Nat.card (Q.neighborSet w)=D)
    (intoA : Q.neighborSet a⊆I) (intoB : Q.neighborSet b⊆I) :
    ∃p∈I,∃q∈I,p≠i ∧ q≠i ∧ p≠q ∧ Q.Adj a p ∧ Q.Adj b q := by
  obtain ⟨p,pa,pi⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({i} : Set X).ncard<(Q.neighborSet a).ncard by rw [Set.ncard_singleton,←Nat.card_coe_set_eq,deg];omega)
  have two := Set.ncard_pair (fun eq : i=p => pi (Set.mem_singleton_iff.mpr eq.symm))
  obtain ⟨q,qb,apart⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({i,p} : Set X).ncard<(Q.neighborSet b).ncard by rw [two,←Nat.card_coe_set_eq,deg];omega)
  exact ⟨p,intoA pa,q,intoB qb,fun eq => pi eq,fun eq => apart (Or.inl eq),
    fun eq => apart (Or.inr eq.symm),pa,qb⟩

/-- The labels chosen by the finite fiber argument produce an actual
D−1 deletion witness on the original host. -/
theorem zero_selected_cut_budget (Q : SimpleGraph X) (I W Z : Set X) (D : ℕ)
    (large : 6≤D) (evenD : Even D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (ind : Q.IsIndepSet I) (cl : Q.IsClique Z) (iw : Disjoint I W) (iz : Disjoint I Z)
    (wz : Disjoint W Z) (cover : I∪W∪Z=Set.univ) (size : Z.ncard=D)
    (holeNeighbors : ∀w∈W,Q.neighborSet w⊆I)
    (i : I) (z z₀ : Z) (a b : W) (zi : Q.Adj z.val i.val) (zz : z≠z₀)
    (ab : a≠b) (ia : Q.Adj i.val a.val) (ib : Q.Adj i.val b.val)
    (rootLoad : ∀j:I,j≠i → ({u:Z|Q.Adj j.val u.val} \ {z₀}).ncard+
      ({w:W|Q.Adj j.val w.val}∩{a,b}).ncard≤D-2) :
    deletionBudget Q (D-1)≤W.ncard := by
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
  obtain ⟨p,pI,q,qI,pi,qi,pq,ap,bq⟩ := select_distinct_mates Q I D (by omega) a.val b.val i.val reg
    (holeNeighbors a.val a.property) (holeNeighbors b.val b.property)
  let cA : ↥(Uᶜ) := ⟨a.val,liveW a.property (Or.inl rfl)⟩
  let cB : ↥(Uᶜ) := ⟨b.val,liveW b.property (Or.inr rfl)⟩
  let cP : ↥(Uᶜ) := ⟨p,liveI pI pi⟩
  let cQ : ↥(Uᶜ) := ⟨q,liveI qI qi⟩
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
    have parity := Nat.even_iff.mp evenD
    omega
  have ac : cA∉C := fun h => Set.disjoint_left.mp wz a.property h.1
  have bc : cB∉C := fun h => Set.disjoint_left.mp wz b.property h.1
  have pc : cP∉C := fun h => Set.disjoint_left.mp iz pI h.1
  have qc : cQ∉C := fun h => Set.disjoint_left.mp iz qI h.1
  have out : ∀x,x∈({cA,cP,cB,cQ} : Set _) → x∉C := by
    rintro x (eq|eq|eq|eq)
    · exact eq ▸ ac
    · exact eq ▸ pc
    · exact eq ▸ bc
    · exact (Set.mem_singleton_iff.mp eq) ▸ qc
  have a_ne_b : cA≠cB := fun eq => ab (Subtype.ext (congrArg (fun v : ↥(Uᶜ) => v.val) eq))
  have a_ne_q : cA≠cQ := by
    intro eq
    have aq : a.val=q := congrArg (fun v : ↥(Uᶜ) => v.val) eq
    exact Set.disjoint_left.mp iw qI (aq ▸ a.property)
  have p_ne_b : cP≠cB := by
    intro eq
    have pb : p=b.val := congrArg (fun v : ↥(Uᶜ) => v.val) eq
    exact Set.disjoint_left.mp iw pI (pb.symm ▸ b.property)
  have p_ne_q : cP≠cQ := fun eq => pq (congrArg Subtype.val eq)
  have sep : Disjoint ({cA,cP} : Set _) {cB,cQ} := by
    apply Set.disjoint_left.mpr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have iRemoved : i.val∈U := Or.inr (Or.inl rfl)
  have zRemoved : z₀.val∈U := Or.inr (Or.inr rfl)
  have lose {x : ↥(Uᶜ)} {y : X} (gone : y∈U) (adj : Q.Adj x.val y) :
      Nat.card (H.neighborSet x)≤D-1 := by
    have cut := degree_loss_for_named_deletion Q U {y} x
      (Set.singleton_subset_iff.mpr gone) (Set.singleton_subset_iff.mpr adj)
    rw [Set.ncard_singleton,reg] at cut
    change Nat.card (H.neighborSet x)+1≤D at cut
    omega
  have rootBound := root_degree_selected_cut Q I W Z ind cover i a b z₀ D rootLoad
  have bounds (x : ↥(Uᶜ)) : Nat.card (H.neighborSet x)≤D-1 ∧
      (Nat.card (H.neighborSet x)=D-1 → x∈C ∨ x=cA ∨ x=cB) := by
    have mem : x.val∈I∪W∪Z := cover ▸ Set.mem_univ _
    rcases mem with (hx|hx)|hx
    · have low : Nat.card (H.neighborSet x)≤D-2 := rootBound x hx; exact ⟨by omega,fun h => by omega⟩
    · have pair : x.val∈({a.val,b.val} : Set X) := by
        by_contra h;exact x.property (Or.inl ⟨hx,h⟩)
      rcases pair with eq|eq
      · exact ⟨lose iRemoved (eq ▸ ia.symm),fun _ => Or.inr (Or.inl (Subtype.ext eq))⟩
      · have eq' := Set.mem_singleton_iff.mp eq
        exact ⟨lose iRemoved (eq' ▸ ib.symm),fun _ => Or.inr (Or.inr (Subtype.ext eq'))⟩
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
        change Nat.card (H.neighborSet x)+2≤D at degree
        omega
      · exact Or.inl ⟨hx,fun h => h.elim eq (fun e => nz (Set.mem_singleton_iff.mp e))⟩
  have remainder := admits_remainder_clique_two_edges H D (by omega) C cc ce cA cB cP cQ ap bq out sep
    (fun x => (bounds x).1) (fun x => (bounds x).2)
  exact (deletionBudget_le_of_witness Q (D-1) U remainder).trans_eq sameSize

#print axioms zero_selected_cut_budget
end JSP452Audit.StarHost
