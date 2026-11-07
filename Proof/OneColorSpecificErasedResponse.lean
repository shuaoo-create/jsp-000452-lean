import TwoColorBudgetExterior
namespace JSP452Audit.StarHost
open SimpleGraph

/-- View the given copy on the full internal-edge restoration without
changing its vertex map, so the established crossing-edge account applies. -/
def liftPaletteCopy {I X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (R P : SimpleGraph X) (sub : P≤restoredInternal G K)
    (n : I→ℕ) (f : (forest n).Copy (R⊔P)) : (forest n).Copy (R⊔restoredInternal G K) :=
  (SimpleGraph.Copy.ofLE _ _ (sup_le_sup_left sub R)).comp f

theorem internal_copy_in_chosen_palette {I X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (R P : SimpleGraph X) (less : R≤eraseInternal G K.core)
    (sub : P≤restoredInternal G K) (n : I→ℕ) (f : (forest n).Copy (R⊔P)) :
    let g := liftPaletteCopy G K R P sub n f
    (forest (fun z:↥(whollyInternal G K R n g) => n z.val)).IsContained (P.induce K.core) := by
  intro g
  let U := whollyInternal G K R n g
  let sel := subforestCopy (fun z:U => n z.val) n (Function.Embedding.subtype _) (fun _ => le_rfl)
  let place (z:Vertices (fun j:U => n j.val)) : K.core := ⟨f (sel z),z.1.property z.2⟩
  refine ⟨{ toHom := {toFun := place,map_rel' := ?_},
            injective' := fun _ _ h => sel.injective (f.injective (congrArg (fun z:K.core => z.val) h)) }⟩
  intro x y e
  rcases f.toHom.map_adj (sel.toHom.map_adj e) with outside|inside
  · exact ((less outside).2 ⟨(place x).property,(place y).property⟩).elim
  · exact inside

/-- Only the matching rank of the chosen internal color can damage this
copy. Its wholly internal stars use that same color. The root budget is
shared with the unchanged vertex labels of the original copy. -/
theorem colored_erased_response {s i old l D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D)
    (R P : SimpleGraph X) (less : R≤eraseInternal G K.core) (sub : P≤restoredInternal G K)
    (W : RemovalBudget s) (n : Fin s→ℕ) (hn : Antitone n) (pn : ∀z,1≤n z)
    (adm : AdmitsInternal W n (P.induce K.core)) (len : i+old=s) (fits : i+l=W.len)
    (f : (forest (fun z:Fin old => n (originalSuffixLabel i old len.le z))).Copy (R⊔P)) :
    (suffixStars (padDemand (commonErasedDemand n W K.roots.ncard (matchingEdges P))) i l).IsContained R := by
  classical
  let m (z:Fin old) := n (originalSuffixLabel i old len.le z)
  let g := liftPaletteCopy G K R P sub m f
  let C := whollyInternal G K R m g
  let U := Cᶜ
  let E := touchedStars R (restoredInternal G K) m g
  let v := survivingSize G K R m g
  let S : Set U := {u | u.val∈E}
  let _ := Fintype.ofFinite ↥U
  have internal := internal_copy_in_chosen_palette G K R P less sub m f
  have inside : originalRemoved i old len.le Uᶜ∈W.choices := by
    change originalRemoved i old len.le Cᶜᶜ∈W.choices
    rw [compl_compl];exact adm i old len.le C internal
  have touches : C⊆E := wholly_internal_touched G K R m g less (fun z => pn _)
  have price : E.toFinite.toFinset.card≤matchingEdges P := by
    rw [←Set.ncard_eq_toFinset_card E E.toFinite]
    exact touchedStars_le_matchingEdges R P m f
  have rootcost : S.toFinite.toFinset.card≤K.roots.ncard := by
    rw [←Set.ncard_eq_toFinset_card S S.toFinite]
    let send (z:S) : ↥(E \ C) := ⟨z.val.val,z.property,z.val.property⟩
    have inj : Function.Injective send := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun z:↥(E \ C) => z.val) eq))
    exact (Nat.card_le_card_of_injective send inj).trans (short_crossing_count G K R m g less)
  have value (z:U) (ok:z.val∉E.toFinite.toFinset) : v z=m z.val := by
    exact if_neg (fun h => ok ((Set.Finite.mem_toFinset _).mpr h))
  have good (z:U) (ok:z∉S.toFinite.toFinset) : v z=m z.val := by
    exact if_neg (fun h => ok ((Set.Finite.mem_toFinset _).mpr h))
  have avoid (z:Fin old) (ok:z∉E.toFinite.toFinset) : z∈U :=
    fun h => ok ((Set.Finite.mem_toFinset _).mpr (touches h))
  have joint := join_same_survivor n hn W len fits U inside v
    (surviving_size_positive G K R m (fun z => pn _) g) E.toFinite.toFinset price avoid value S.toFinite.toFinset rootcost good
  exact joint.trans (actual_surviving_copy G K R less m g)

#print axioms internal_copy_in_chosen_palette
#print axioms colored_erased_response
end JSP452Audit.StarHost
