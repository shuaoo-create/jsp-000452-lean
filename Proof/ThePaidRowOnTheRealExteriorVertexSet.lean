import ExposureOnTheSecondActualTenDegreeExteriorStage
namespace JSP452Audit.StarHost
open SimpleGraph
theorem restrict_copy_to_incident_labels {X Z : Type*} (G C : SimpleGraph X) (T:Set X) (inside:∀{x y},G.Adj x y → x∈T) (A : SimpleGraph Z)
    (sub : C ≤ G) (positive : ∀ z, ∃ w, A.Adj z w) (copy : A.IsContained C) :
    A.IsContained (C.induce T) := by
  obtain ⟨f⟩ := copy
  have lands (z : Z) : f z ∈ T := by
    obtain ⟨w,edge⟩ := positive z
    exact inside (sub (f.toHom.map_adj edge))
  let lift : A →g C.induce T := ⟨fun z => ⟨f z,lands z⟩,fun edge => f.toHom.map_adj edge⟩
  exact ⟨lift.toCopy (fun _ _ eq => f.injective (congrArg Subtype.val eq))⟩

/-- Every coloring of the support extends along the original-label inclusion.
Positive forest copies of either color restrict back to the same support. -/
theorem forces_on_incident_labels {X I J : Type*} (G : SimpleGraph X) (T:Set X) (inside:∀{x y},G.Adj x y → x∈T) (n : I → ℕ) (m : J → ℕ)
    (pn : ∀ i, 0 < n i) (pm : ∀ j, 0 < m j) (force : Forces G (forest n) (forest m)) :
    Forces (G.induce T) (forest n) (forest m) := by
  intro R sub
  let C := R.spanningCoe
  have original : C ≤ G := (map_monotone _ sub).trans (G.spanningCoe_induce_le _)
  rcases force C original with red | blue
  · left
    simpa only [C,induce_spanningCoe] using
      restrict_copy_to_incident_labels G C T inside _ original (forest_has_neighbor n pn) red
  · right
    have copied := restrict_copy_to_incident_labels G (G \ C) T inside _ sdiff_le (forest_has_neighbor m pm) blue
    have eq : (G \ C).induce T = (G.induce T) \ R := by
      ext x y
      change (G.Adj x.val y.val ∧ ¬C.Adj x.val y.val) ↔
        (G.Adj x.val y.val ∧ ¬R.Adj x y)
      have inside : C.Adj x.val y.val ↔ R.Adj x y :=
        show (R.map (Function.Embedding.subtype _)).Adj x.val y.val ↔ R.Adj x y from map_adj_apply
      rw [inside]
    rwa [eq] at copied


theorem erased_closed_exterior_forcing_row {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (V:Set ↥(Uᶜ:Set X)) {s t r:ℕ} (n m:ℕ→ℕ)
    (pn:∀i<s,0<n i) (pm:∀j<t,0<m j)
    (row:ForcingRow ((eraseInternal G U).induce (Subtype.val '' V)ᶜ) s t n m r) :
    ForcingRow ((G.induce Uᶜ).induce Vᶜ) s t n m r := by
  let S := (Subtype.val '' V)ᶜ
  let Y := (eraseInternal G U).induce S
  let T : Set S := {v|v.val∈Uᶜ}
  have inside {a b:↥S} (edge:Y.Adj a b) : a∈T := fun h => edge.2 ⟨h,closed _ h _ edge.1⟩
  let send (x:↥(Vᶜ:Set ↥(Uᶜ:Set X))) : T :=
    ⟨⟨x.val.val,by rintro ⟨v,hv,eq⟩;exact x.property ((Subtype.ext eq : v=x.val) ▸ hv)⟩,x.val.property⟩
  let back (y:↥T) : ↥(Vᶜ:Set ↥(Uᶜ:Set X)) :=
    let v : ↥(Uᶜ:Set X) := ⟨y.val.val,y.property⟩
    ⟨v,fun h => y.val.property ⟨v,h,rfl⟩⟩
  let e : (G.induce Uᶜ).induce Vᶜ ≃g Y.induce T := {
    toEquiv := {toFun := send,invFun := back,left_inv := fun _ => rfl,right_inv := fun _ => rfl}
    map_rel_iff' := fun {v _} => ⟨fun adj => adj.1,fun adj => ⟨adj,fun h => v.val.property h.1⟩⟩ }
  apply forcingRow_of_iso e.symm
  intro i j l q ij il jq pl pq
  exact forces_on_incident_labels Y T inside (fun z:Fin l => n (i+z.val)) (fun z:Fin q => m (j+z.val))
    (fun z => pn _ (by have := z.isLt;omega)) (fun z => pm _ (by have := z.isLt;omega))
    (row i j l q ij il jq pl pq)


#print axioms forces_on_incident_labels
#print axioms erased_closed_exterior_forcing_row
end JSP452Audit.StarHost
