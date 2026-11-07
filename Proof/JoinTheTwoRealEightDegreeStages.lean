import TheOnlyOuterEdgeCorrectionIsTwoPorts
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem actual_second_stage (H : ThreeDegreeStages R.erased 7) (capY : ∀v,Nat.card (R.erased.neighborSet v)≤9)
    (I : Set X) (inside : I⊆R.chosen) (tips : R.tips⊆I)
    (cap1 : ∀v,Nat.card ((G.induce (I∪H.upper)ᶜ).neighborSet v)≤8) :
    ∃I' : Set X,I⊆I' ∧ I'⊆R.chosen ∧
      (I∪H.upper).ncard≤(I'∪H.midCut).ncard ∧
      (∀v,Nat.card ((G.induce (I'∪H.midCut)ᶜ).neighborSet v)≤7) ∧
      (G.induce (I'∪H.midCut)ᶜ).edgeSet.ncard+8*((I'∪H.midCut).ncard-(I∪H.upper).ncard)≤
        (G.induce (I∪H.upper)ᶜ).edgeSet.ncard+2 := by
  let B := H.upper
  let C := H.midCut
  let U := R.chosen\I
  let S := I∪B
  obtain ⟨off,costO⟩ := R.second_exterior_cut_cost H
  have apart := R.full_stage_off_boxes B H.first
  let split := R.split_after_original_deletions I B inside tips apart
  let left : G.induce U ↪g (G.induce U⊕g G.induce (R.outer B)) := Embedding.sumInl
  have lim := degree_cap_along_copy (split.toCopy.comp left.toCopy) 8 cap1
  obtain ⟨J,stage⟩ := complete_degree_stage_exists (G.induce U) 8
  let J' := Subtype.val '' J
  let I' := I∪J'
  let T := I'∪C
  have subJ : J'⊆U := by rintro _ ⟨j,_,rfl⟩;exact j.property
  have inW : I'⊆R.chosen := Set.union_subset inside (subJ.trans Set.sdiff_subset)
  have has : I⊆I' := Set.subset_union_left
  have disIJ : Disjoint I J' := Set.disjoint_left.mpr (fun _ i j => (subJ j).2 i)
  have sizeJ : J'.ncard=J.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have sizeI : I'.ncard=I.ncard+J.ncard := (Set.ncard_union_eq disIJ).trans (by rw [sizeJ])
  have sz1 : S.ncard=I.ncard+B.ncard := Set.ncard_union_eq (apart.symm.mono_left inside)
  have sz2 : T.ncard=I'.ncard+C.ncard := Set.ncard_union_eq (off.symm.mono_left inW)
  have ext := nested_removed_card H.upper H.middle
  change C.ncard=B.ncard+H.middle.ncard at ext
  have spent : T.ncard-S.ncard=J.ncard+H.middle.ncard := by omega
  have eq : U\J'=R.chosen\I' := by
    ext v
    exact ⟨fun h => ⟨h.1.1,fun into => into.elim h.1.2 h.2⟩,
      fun h => ⟨⟨h.1,fun i => h.2 (Or.inl i)⟩,fun j => h.2 (Or.inr j)⟩⟩
  have iso : Nonempty (((G.induce U).induce Jᶜ) ≃g G.induce (R.chosen\I')) := by
    rw [←eq];exact ⟨strip_inside_labels G U J⟩
  obtain ⟨core⟩ := iso
  let final := R.split_after_original_deletions I' C inW (tips.trans has) off
  have low := complete_stage_lowers_cap (G.induce U) 8 J lim stage
  have inCap := degree_cap_along_copy core.symm.toCopy 7 (fun v => by have := low v;omega)
  have oCap := degree_cap_along_copy (R.outer_copy C) 7 (H.degree_caps capY).2.1
  have cap2 := cap_on_sum_after_relabeling final 7 inCap oCap
  have firstEdges : (G.induce U⊕g G.induce (R.outer B)).edgeSet.ncard=(G.induce Sᶜ).edgeSet.ncard :=
    Nat.card_congr split.mapEdgeSet
  have nextEdges : (G.induce (R.chosen\I')⊕g G.induce (R.outer C)).edgeSet.ncard=(G.induce Tᶜ).edgeSet.ncard :=
    Nat.card_congr final.mapEdgeSet
  rw [edge_ncard_sumGraph] at firstEdges nextEdges
  have price := JSP452Audit.StarHost.degree_on_independent_full_set (G.induce U) J 8 stage.2.1 stage.1
  have coreEdges : ((G.induce U).induce Jᶜ).edgeSet.ncard=(G.induce (R.chosen\I')).edgeSet.ncard :=
    Nat.card_congr core.mapEdgeSet
  rw [coreEdges] at price
  change (G.induce (R.outer C)).edgeSet.ncard+8*H.middle.ncard≤(G.induce (R.outer B)).edgeSet.ncard+2 at costO
  refine ⟨I',has,inW,by change S.ncard≤T.ncard;omega,cap2,?_⟩
  change (G.induce Tᶜ).edgeSet.ncard+8*(T.ncard-S.ncard)≤(G.induce Sᶜ).edgeSet.ncard+2
  omega

#print axioms actual_second_stage
end JSP452Audit.StarHost.NinePortRegion
