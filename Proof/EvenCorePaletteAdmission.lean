import BothFixedPaletteRows
open private JSP452Audit.StarHost.reindex_internal_copy from ComponentOrderRemovalBudget
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Original internal edges meeting an actual marked core vertex are
red. The complementary internal blue graph avoids all marked labels. -/
def incidentPalette {X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (U : Set K.core) : SimpleGraph X where
  Adj x y := (restoredInternal G K).Adj x y ∧ (x∈Subtype.val '' U ∨ y∈Subtype.val '' U)
  symm := ⟨fun _ _ e => ⟨e.1.symm,e.2.symm⟩⟩
  loopless := ⟨fun x e => (restoredInternal G K).loopless.irrefl x e.1⟩

theorem incident_palette_rank {X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (U : Set K.core) : matchingEdges (incidentPalette G K U)≤U.ncard := by
  have bound := matchingEdges_le_cover_card (incidentPalette G K U) (Subtype.val '' U) (fun _ _ e => e.2)
  rwa [Set.ncard_image_of_injective _ Subtype.val_injective] at bound

theorem blue_palette_residual_copy {X I : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (U : Set K.core) (n : I→ℕ) (pn : ∀i,1≤n i)
    (copy : (forest n).IsContained (((restoredInternal G K) \ incidentPalette G K U).induce K.core)) :
    (forest n).IsContained ((G.induce K.core).induce Uᶜ) := by
  obtain ⟨f⟩ := copy
  have away (x:Vertices n) : f x∉U := by
    intro inside
    obtain ⟨y,adj⟩ := forest_has_neighbor n pn x
    have e := f.toHom.map_adj adj
    exact e.2 ⟨e.1,Or.inl ⟨f x,inside,rfl⟩⟩
  exact ⟨{ toHom := { toFun := fun x => ⟨f x,away x⟩,map_rel' := fun adj => (f.toHom.map_adj adj).1.1 },
           injective' := fun _ _ h => f.injective (congrArg (fun z:↥(Uᶜ : Set K.core) => z.val) h) }⟩

noncomputable def halfOrderBudget {t : ℕ} (m : Fin t→ℕ) (b : ℕ) : RemovalBudget t := by
  classical
  let opts := Finset.univ.filter (fun T:Finset (Fin t) => (∑z:↥T,(m z.val+1)/2)≤b)
  exact ⟨opts,∅,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp⟩⟩

theorem mem_half_order_budget {t : ℕ} (m : Fin t→ℕ) (b : ℕ) (T : Finset (Fin t)) :
    T∈(halfOrderBudget m b).choices ↔ (∑z:↥T,(m z.val+1)/2)≤b := by
  classical
  exact ⟨fun mem => (Finset.mem_filter.mp mem).2,fun ok => Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok⟩⟩

theorem half_order_residual_nonempty {t : ℕ} (m : Fin t→ℕ) (b : ℕ) (large : b<∑j,(m j+1)/2) :
    0<(halfOrderBudget m b).len := by
  classical
  let W := halfOrderBudget m b
  obtain ⟨T,mem,eq⟩ := Finset.exists_mem_eq_sup W.choices W.present Finset.card
  have valid := (mem_half_order_budget m b T).mp mem
  change W.loss=T.card at eq
  by_contra! zero
  change W.len≤0 at zero
  have cap := W.loss_le_order
  have sz : T.card=t := by dsimp only [RemovalBudget.len] at zero;omega
  have total : T=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [sz])
  subst T
  have all : (∑z:↥(Finset.univ:Finset (Fin t)),(m z.val+1)/2)=∑j,(m j+1)/2 := by
    exact (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) (fun j:Fin t => (m j+1)/2)).symm
  omega

/-- A fixed even cut pays half-order units on the genuine blue residual.
The condition holds for every legally shifted original suffix at once. -/
theorem even_palette_admission {t D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    [Fintype (G.induce K.core).ConnectedComponent] (m : Fin t→ℕ) (pm : ∀j,1≤m j)
    (U : Set K.core) (w : ℕ) (charge : (∑c:(G.induce K.core).ConnectedComponent,(c.supp∩U).ncard/2)=w) :
    AdmitsInternal (halfOrderBudget m (matchingEdges (G.induce K.core)-w)) m
      (((restoredInternal G K) \ incidentPalette G K U).induce K.core) := by
  classical
  intro i l hl A copy
  let T := originalRemoved i l hl A
  have full := JSP452Audit.StarHost.reindex_internal_copy hl A m _ copy
  obtain ⟨f⟩ := blue_palette_residual_copy G K U (fun z:↥T => m z.val) (fun z => pm z.val) full
  have bound := critical_half_orders_off_cover (G.induce K.core) (fun z:↥T => m z.val) U f
    (ordinary_core_components_critical G K)
  rw [charge] at bound
  exact (mem_half_order_budget m _ T).mpr (by omega)

#print axioms incident_palette_rank
#print axioms blue_palette_residual_copy
#print axioms half_order_residual_nonempty
#print axioms even_palette_admission
end JSP452Audit.StarHost
