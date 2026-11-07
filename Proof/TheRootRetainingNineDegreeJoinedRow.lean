import OneOriginalForestAfterErasingBothNineBoxes
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph

theorem complete_red_response_in_erased_core {s i old l : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : NinePortRegion G) (R : SimpleGraph X) (less : R≤eraseInternal G K.chosen)
    (W : RemovalBudget s) (n : Fin s→ℕ) (hn : Antitone n) (pn : ∀z,1≤n z)
    (adm : AdmitsInternal W n (G.induce K.chosen)) (len : i+old=s) (fits : i+l=W.len)
    (f : (forest (fun z:Fin old => n (originalSuffixLabel i old len.le z))).Copy (R⊔restoredInternal G K)) :
    (suffixStars (padDemand (commonErasedDemand n W K.roots.ncard (matchingEdges (G.induce K.chosen)))) i l).IsContained R := by
  classical
  let m (z:Fin old) := n (originalSuffixLabel i old len.le z)
  let C := whollyInternal G K R m f
  let U := Cᶜ
  let E := touchedStars R (restoredInternal G K) m f
  let v := survivingSize G K R m f
  let S : Set U := {u | u.val∈E}
  let _ := Fintype.ofFinite ↥U
  have internal := actual_wholly_internal G K R m f less
  have inside : originalRemoved i old len.le Uᶜ∈W.choices := by
    change originalRemoved i old len.le Cᶜᶜ∈W.choices
    rw [compl_compl];exact adm i old len.le C internal
  have touches : C⊆E := wholly_internal_touched G K R m f less (fun z => pn _)
  have price : E.toFinite.toFinset.card≤matchingEdges (G.induce K.chosen) := by
    rw [←Set.ncard_eq_toFinset_card E E.toFinite]
    have rk := touchedStars_le_matchingEdges R (restoredInternal G K) m f
    rw [show matchingEdges (restoredInternal G K)=matchingEdges (G.induce K.chosen) from rank_of_internal_edges G K.chosen] at rk
    exact rk
  have rootcost : S.toFinite.toFinset.card≤K.roots.ncard := by
    rw [←Set.ncard_eq_toFinset_card S S.toFinite]
    let send (z:S) : ↥(E \ C) := ⟨z.val.val,z.property,z.val.property⟩
    have inj : Function.Injective send := fun _ _ eq => Subtype.ext (Subtype.ext (congrArg (fun z:↥(E \ C) => z.val) eq))
    exact (Nat.card_le_card_of_injective send inj).trans (short_crossing_count G K R m f less)
  have basic (z:U) (ok:z.val∉E.toFinite.toFinset) : v z=m z.val := by
    exact if_neg (fun h => ok ((Set.Finite.mem_toFinset _).mpr h))
  have good (z:U) (ok:z∉S.toFinite.toFinset) : v z=m z.val := by
    exact if_neg (fun h => ok ((Set.Finite.mem_toFinset _).mpr h))
  have avoid (z:Fin old) (ok:z∉E.toFinite.toFinset) : z∈U :=
    fun h => ok ((Set.Finite.mem_toFinset _).mpr (touches h))
  have joined := join_same_survivor n hn W len fits U inside v
    (surviving_size_positive G K R m (fun z => pn _) f) E.toFinite.toFinset price avoid basic S.toFinite.toFinset rootcost good
  exact joined.trans (actual_surviving_copy G K R less m f)

/-- For the same budget list used on the exterior, restoring red core
edges proves the joined complete forcing row on Z with all roots retained. -/
theorem complete_erased_core_row {s t r : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : NinePortRegion G) (W : RemovalBudget s)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (pn : ∀z,1≤n z)
    (adm : AdmitsInternal W n (G.induce K.chosen)) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ForcingRow (eraseInternal G K.chosen) W.len t
      (padDemand (commonErasedDemand n W K.roots.ncard (matchingEdges (G.induce K.chosen)))) (padDemand m) r := by
  intro i j l q idx fits jq pos posb R sub
  let old := s-i
  have room : W.len≤s := Nat.sub_le _ _
  have len : i+old=s := by dsimp [old];omega
  have orig := row i j old q idx len jq (by omega) posb
  have less : R⊔restoredInternal G K≤G := sup_le (sub.trans (eraseInternal_le G K.chosen)) sdiff_le
  rcases orig _ less with red|blue
  · let oldN (z:Fin old) := n (originalSuffixLabel i old len.le z)
    have eq : (fun z:Fin old => padDemand n (i+z.val))=oldN := by
      funext z;exact dif_pos (originalSuffixLabel i old len.le z).isLt
    change (forest (fun z:Fin old => padDemand n (i+z.val))).IsContained _ at red
    rw [eq] at red
    obtain ⟨f⟩ := red
    exact Or.inl (complete_red_response_in_erased_core G K R sub W n hn pn adm len fits f)
  · right
    apply blue.mono_right
    intro x y e
    refine ⟨?_,fun red => e.2 (Or.inl red)⟩
    by_contra lost
    exact e.2 (Or.inr ⟨e.1,lost⟩)

#print axioms complete_red_response_in_erased_core
#print axioms complete_erased_core_row
end JSP452Audit.StarHost.NinePortRegion
