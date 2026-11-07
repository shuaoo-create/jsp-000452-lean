import EvenDeletionsOnAllActualTenDegreeComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
namespace TenBlockPartition
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : TenBlockPartition G)

theorem copies_without_roots_stay_outside {I : Type*} (n : I→ℕ) (pn : ∀i,1≤n i) (U : Set X)
    (f : (forest n).Copy (R.retainedEdges.induce (R.roots∪U)ᶜ)) :
    (forest n).IsContained (G.induce R.rest) := by
  have land (z : Vertices n) : (f z).val∈R.rest := by
    have away : (f z).val∉R.roots := fun root => (f z).property (Or.inl root)
    obtain ⟨y,edge⟩ := forest_has_neighbor n pn z
    have old := f.toHom.map_adj edge
    have out : (f z).val∉R.core := by
      intro ins
      have ext : (f y).val∉R.core := fun h => old.2 ⟨ins,h⟩
      have root := R.chosen_external_root G ins ext old.1
      exact (f y).property (Or.inl root)
    have mem : (f z).val∈R.roots∪R.core∪R.rest := R.cover.symm ▸ Set.mem_univ _
    exact mem.resolve_left (fun h => h.elim away out)
  let send (z : Vertices n) : R.rest := ⟨(f z).val,land z⟩
  refine ⟨{toHom := {toFun := send,map_rel' := fun e => (f.toHom.map_rel' e).1},injective' := ?_}⟩
  exact fun _ _ eq => f.injective (Subtype.ext (congrArg (fun v : R.rest => v.val) eq))

theorem two_real_axis_inventories {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (w : ℕ) (fit : w≤R.capacity)
    (tooLarge : R.capacity-w<∑i,(m i+1)/2) :
    ∀h,0<h →
      (originalThresholdCount n h-2*w-(r+R.roots.ncard)≤uniformEnvelope (G.induce R.rest) h ∧
      originalThresholdCount n h-2*w-r≤uniformEnvelope R.retainedEdges h) := by
  obtain ⟨U,inside,size,limit⟩ := R.even_cut_on_actual_components.{u,0} w fit
  have no : ¬(forest m).IsContained (G.induce (R.core\U)) := fun copy => (Nat.not_le_of_lt tooLarge) (limit m copy)
  let T := R.roots∪U
  have count : T.ncard=R.roots.ncard+2*w := (Set.ncard_union_eq (R.rootsCore.mono_right inside)).trans (by rw [size])
  intro h pos
  constructor
  · by_cases live : r+T.ncard<originalThresholdCount n h
    · obtain ⟨f⟩ := even_cut_red_packing G R.core U T Set.subset_union_right n m ht hn hm pn pm row live no
      have real := R.copies_without_roots_stay_outside (fun _ => h) (fun _ => pos) U f
      have price := uniform_copy_costs_unit_width _ _ h pos real
      omega
    · omega
  · by_cases live : r+U.ncard<originalThresholdCount n h
    · have copy := even_cut_red_packing G R.core U U Set.Subset.rfl n m ht hn hm pn pm row live no
      have real := copy.trans ⟨(Embedding.induce (G:=R.retainedEdges) Uᶜ).toCopy⟩
      have price := uniform_copy_costs_unit_width _ _ h pos real
      omega
    · omega

#print axioms copies_without_roots_stay_outside
#print axioms two_real_axis_inventories
end TenBlockPartition
end JSP452Audit.StarHost
