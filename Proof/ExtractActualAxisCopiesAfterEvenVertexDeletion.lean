import FullBlueAvoidanceForcesAUniformRedPacking
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem blue_after_internal_erasure_copies_inside {X : Type*} [Finite X] {t : ℕ} (G : SimpleGraph X)
    (W U T : Set X) (removed : U⊆T) (m : Fin t→ℕ) (pm : ∀i,1≤m i)
    (copy : (forest m).IsContained ((G.induce Tᶜ)\((eraseInternal G W).induce Tᶜ))) :
    (forest m).IsContained (G.induce (W\U)) := by
  obtain ⟨f⟩ := copy
  have inside (z : Vertices m) : (f z).val∈W\U := by
    obtain ⟨v,edge⟩ := forest_has_neighbor m pm z
    have hit := f.toHom.map_adj edge
    have mem : (f z).val∈W := by
      by_contra no;exact hit.2 ⟨hit.1,fun pair => no pair.1⟩
    exact ⟨mem,fun u => (f z).property (removed u)⟩
  let send (z : Vertices m) : ↥(W\U) := ⟨(f z).val,inside z⟩
  refine ⟨{toHom := {toFun := send,map_rel' := fun edge => (f.toHom.map_rel' edge).1},injective' := ?_}⟩
  exact fun _ _ eq => f.injective (Subtype.ext (congrArg (fun v : ↥(W\U) => v.val) eq))

theorem even_cut_red_packing {X : Type*} [Finite X] (G : SimpleGraph X) (W U T : Set X) (removed : U⊆T)
    {s t r h : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀i,1≤m i) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : r+T.ncard<originalThresholdCount n h) (no : ¬(forest m).IsContained (G.induce (W\U))) :
    (forest (fun _ : Fin (originalThresholdCount n h-(r+T.ncard)) => h)).IsContained
      ((eraseInternal G W).induce Tᶜ) := by
  let H := G.induce Tᶜ
  let A := (eraseInternal G W).induce Tᶜ
  have current := row_delete_set G T _ _ (pad_antitone n hn) (pad_antitone m hm) (pad_positive n pn)
    (pad_positive m pm) row
  exact full_blue_avoidance_red_suffix H A (fun _ _ e => e.1) ht n m hn current live
    (fun copy => no (blue_after_internal_erasure_copies_inside G W U T removed m pm copy))

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem copies_without_roots_stay_outside {I : Type*} (n : I→ℕ) (pn : ∀i,1≤n i) (U : Set X)
    (f : (forest n).Copy (R.retainedEdges.induce (R.roots∪U)ᶜ)) :
    (forest n).IsContained (G.induce R.outside) := by
  have land (z : Vertices n) : (f z).val∈R.outside := by
    have away : (f z).val∉R.roots := fun root => (f z).property (Or.inl root)
    obtain ⟨y,edge⟩ := forest_has_neighbor n pn z
    have old := f.toHom.map_adj edge
    have out : (f z).val∉R.chosen := by
      intro ins
      have ext : (f y).val∉R.chosen := fun h => old.2 ⟨ins,h⟩
      have root := R.chosen_external_root G ins ext old.1
      exact (f y).property (Or.inl root)
    exact fun h => h.elim away out
  let send (z : Vertices n) : R.outside := ⟨(f z).val,land z⟩
  refine ⟨{toHom := {toFun := send,map_rel' := fun e => (f.toHom.map_rel' e).1},injective' := ?_}⟩
  exact fun _ _ eq => f.injective (Subtype.ext (congrArg (fun v : R.outside => v.val) eq))

theorem two_real_axis_inventories {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (w : ℕ) (fit : w≤R.totalCapacity)
    (tooLarge : R.totalCapacity-w<∑i,(m i+1)/2) :
    ∀h,0<h →
      (originalThresholdCount n h-2*w-(r+R.roots.ncard)≤uniformEnvelope (G.induce R.outside) h ∧
      originalThresholdCount n h-2*w-r≤uniformEnvelope R.retainedEdges h) := by
  obtain ⟨U,inside,size,limit⟩ := R.even_cut_on_two_boxes.{u,0} w fit
  have no : ¬(forest m).IsContained (G.induce (R.chosen\U)) := fun copy => (Nat.not_le_of_lt tooLarge) (limit m copy)
  let T := R.roots∪U
  have count : T.ncard=R.roots.ncard+2*w := (Set.ncard_union_eq (R.chosen_away.mono_right inside)).trans (by rw [size])
  intro h pos
  constructor
  · by_cases live : r+T.ncard<originalThresholdCount n h
    · obtain ⟨f⟩ := even_cut_red_packing G R.chosen U T Set.subset_union_right n m ht hn hm pn pm row live no
      have real := R.copies_without_roots_stay_outside (fun _ => h) (fun _ => pos) U f
      have price := uniform_copy_costs_unit_width _ _ h pos real
      omega
    · omega
  · by_cases live : r+U.ncard<originalThresholdCount n h
    · have copy := even_cut_red_packing G R.chosen U U Set.Subset.rfl n m ht hn hm pn pm row live no
      have real := copy.trans ⟨(Embedding.induce (G:=R.retainedEdges) Uᶜ).toCopy⟩
      have price := uniform_copy_costs_unit_width _ _ h pos real
      omega
    · omega

#print axioms copies_without_roots_stay_outside
#print axioms two_real_axis_inventories
end NinePortRegion
#print axioms blue_after_internal_erasure_copies_inside
#print axioms even_cut_red_packing
end JSP452Audit.StarHost
