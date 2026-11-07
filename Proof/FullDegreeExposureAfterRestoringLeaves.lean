import ASecondSlotSavingOnTheSameNineErasure
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

/-- Restore any number of pendant or isolated vertices, including leaves at
a common root. Every previously unmatched root gaining a neighbor can take
one of its own leaves. Extend while preserving the resulting vertex cover. -/
theorem exposure_after_restoring_leaves {X : Type u} [Finite X] (G : SimpleGraph X)
    (L : Set X) (D : ℕ) (high : 2≤D) (leaf : ∀v∈L,Nat.card (G.neighborSet v)≤1) :
    minimumExposure G D≤minimumExposure (G.induce Lᶜ) D := by
  classical
  let H := G.induce Lᶜ
  obtain ⟨M,hm,_,opt⟩ := minimumExposure_attained H D
  let inc := SimpleGraph.Embedding.induce (G:=G) Lᶜ
  let P := M.map inc.toHom
  have pm := hm.map inc.toHom inc.injective
  have support : P.verts=Subtype.val '' M.verts := rfl
  let U : Set X := {v | v∉L ∧ v∉P.verts ∧ ∃w∈L,G.Adj v w}
  let pick (i : U) := i.property.2.2.choose
  have inL (i : U) : pick i∈L := i.property.2.2.choose_spec.1
  have bridge (i : U) : G.Adj i.val (pick i) := i.property.2.2.choose_spec.2
  let root : U↪X := ⟨Subtype.val,Subtype.val_injective⟩
  let tip : U↪X := ⟨pick,by
    intro i j eq
    have one : (G.neighborSet (pick i)).ncard≤1 := leaf (pick i) (inL i)
    apply Subtype.ext
    apply ((Set.ncard_le_one (s:=G.neighborSet (pick i))).mp one)
    · exact (bridge i).symm
    · exact eq.symm ▸ (bridge j).symm⟩
  have apart : Disjoint (Set.range root) (Set.range tip) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,eq⟩
    change pick j=i.val at eq
    exact i.property.1 (eq ▸ inL j)
  let Q := pairFamily G root tip bridge
  have qm := pairFamily_isMatching G root tip bridge apart
  have dis : Disjoint P.verts Q.verts := by
    apply Set.disjoint_left.mpr
    rintro v pv (⟨i,rfl⟩|⟨i,rfl⟩)
    · exact i.property.2.1 pv
    · rw [support] at pv
      obtain ⟨j,_,eq⟩ := pv
      exact j.property (eq.symm ▸ inL i)
  have union := matching_sup_of_disjoint_verts G pm qm dis
  obtain ⟨N,nm,maxN,cover⟩ := exists_maximum_matching_covering G (P⊔Q) union
  have lift : exposedFull G N D⊆Subtype.val '' exposedFull H M D := by
    intro v ev
    have outside : v∉L := fun vl => by have deg := leaf v vl;have full := ev.2;omega
    let x : ↥(Lᶜ : Set X) := ⟨v,outside⟩
    have miss : v∉P.verts := fun pv => ev.1 (cover (Or.inl pv))
    have no : ¬∃w∈L,G.Adj v w := by
      intro some
      let i : U := ⟨v,outside,miss,some⟩
      exact ev.1 (cover (Or.inr (show v∈Q.verts from Or.inl ⟨i,rfl⟩)))
    have keeps : G.neighborSet v⊆Lᶜ := fun w adj wl => no ⟨w,wl,adj⟩
    have degree : Nat.card (H.neighborSet x)=D := by
      change Nat.card ((G.induce Lᶜ).neighborSet x)=D
      rw [induced_degree_intersection,Set.inter_eq_left.mpr keeps,←Nat.card_coe_set_eq]
      exact ev.2
    exact ⟨x,⟨fun mx => miss (support.symm ▸ ⟨x,mx,rfl⟩),degree⟩,rfl⟩
  have number := Set.ncard_le_ncard lift
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,opt] at number
  exact (minimumExposure_le G D N nm maxN).trans number

#print axioms exposure_after_restoring_leaves
end JSP452Audit.StarHost
