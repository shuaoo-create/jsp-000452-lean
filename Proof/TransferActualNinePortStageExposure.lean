import ThePortDebtOfTheActualFirstStage
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem no_cross_after_tips (I B : Set X) (tips : R.tips⊆I) {x y : X}
    (xin : x∈R.chosen\(I∪B)) (out : y∉R.chosen) : ¬G.Adj x y := by
  intro edge
  have side (i : Fin 2) (box : x∈R.box i) (inc : R.box i⊆R.chosen) : False := by
    have ends := (R.port i).only x box y (fun h => out (inc h)) edge
    exact xin.2 (Or.inl (tips (show x∈R.tips from ⟨i,ends.1.symm⟩)))
  exact xin.1.elim (fun h => side 0 h Set.subset_union_left) (fun h => side 1 h Set.subset_union_right)

/-- Compare any pair of real deletion sets at once. This also applies to
cumulative later stages provided the first two tips are still deleted. -/
theorem actual_stage_exposure_transfer (I B : Set X) (inside : I⊆R.chosen) (tips : R.tips⊆I)
    (D : ℕ) (high : 2≤D) :
    minimumExposure (R.erased.induce Bᶜ) D≤minimumExposure (G.induce (I∪B)ᶜ) D := by
  let W := R.chosen
  let O := (W∪B)ᶜ
  let U := W\(I∪B)
  let S := (I∪B)ᶜ
  let L : Set ↥(Bᶜ : Set X) := {v | v.val∈W}
  have leaves (v) (mem : v∈L) : Nat.card ((R.erased.induce Bᶜ).neighborSet v)≤1 :=
    (induced_neighbor_count_le R.erased Bᶜ v).trans (R.erased_core_degree v.val mem)
  have restore := exposure_after_restoring_leaves (R.erased.induce Bᶜ) L D high leaves
  have ob : O⊆Bᶜ := fun _ h b => h (Or.inr b)
  have labels : Lᶜ={x : ↥(Bᶜ : Set X) | x.val∈O} := by
    ext x
    exact ⟨fun h mem => mem.elim h x.property,fun h w => h (Or.inl w)⟩
  have same : R.erased.induce O=G.induce O := by
    ext x y;exact R.erased_edges_off_boxes (fun w => x.property (Or.inl w)) (fun w => y.property (Or.inl w))
  rw [labels,minimumExposure_iso (original_induced_subset_iso R.erased Bᶜ O ob),same] at restore
  have cover : U∪O=S := by
    ext x
    constructor
    · rintro (u|outside)
      · exact u.2
      · exact fun h => h.elim (fun i => outside (Or.inl (inside i))) (fun b => outside (Or.inr b))
    · intro h
      by_cases w : x∈W
      · exact Or.inl ⟨w,h⟩
      · exact Or.inr (fun a => a.elim w (fun b => h (Or.inr b)))
  have apart : Disjoint U O := Set.disjoint_left.mpr (fun _ u o => o (Or.inl u.1))
  let iso := regionSumIso G S U O cover apart (fun _ u _ o => R.no_cross_after_tips I B tips u (fun w => o (Or.inl w)))
  have sum := minimumExposure_iso iso D
  rw [minimumExposure_sumGraph] at sum
  change minimumExposure (R.erased.induce Bᶜ) D≤minimumExposure (G.induce S) D
  omega

theorem original_cap_after_joining_first_stage (cap : ∀x,Nat.card (G.neighborSet x)≤9)
    (I B : Set X) (tips : R.tips⊆I) (dom : ∀x∈R.chosen,x∈I ∨ ∃y∈I,G.Adj x y)
    (stage : CompleteDegreeStage R.erased 9 B) :
    ∀v : ↥((I∪B)ᶜ : Set X),Nat.card ((G.induce (I∪B)ᶜ).neighborSet v)≤8 := by
  have capY (x) : Nat.card (R.erased.neighborSet x)≤9 := by
    have sub : R.erased.neighborSet x⊆G.neighborSet x := fun _ h => h.1
    exact (Set.ncard_le_ncard sub).trans (cap x)
  have low := complete_stage_lowers_cap R.erased 9 B capY stage
  intro v
  by_cases box : v.val∈R.chosen
  · have hit := (dom v.val box).resolve_left (fun i => v.property (Or.inl i))
    obtain ⟨y,yi,e⟩ := hit
    by_contra! high
    have max := induced_neighbor_count_le G (I∪B)ᶜ v
    have degree : Nat.card ((G.induce (I∪B)ᶜ).neighborSet v)=9 := by have := cap v.val;omega
    have original : Nat.card (G.neighborSet v.val)=9 := by have := cap v.val;omega
    have all := all_neighbors_survive_of_induced_full G (I∪B)ᶜ v 9 original.le degree y e
    exact all (Or.inl yi)
  · let w : ↥(Bᶜ : Set X) := ⟨v.val,fun b => v.property (Or.inr b)⟩
    let send (u : (G.induce (I∪B)ᶜ).neighborSet v) : (R.erased.induce Bᶜ).neighborSet w := by
      have out : u.val.val∉R.chosen := fun h => R.no_cross_after_tips I B tips
        ⟨h,u.val.property⟩ box u.property.symm
      exact ⟨⟨u.val.val,fun b => u.val.property (Or.inr b)⟩,(R.erased_edges_off_boxes box out).mpr u.property⟩
    have inj : Function.Injective send := fun _ _ eq =>
      Subtype.ext (Subtype.ext (congrArg (fun z : (R.erased.induce Bᶜ).neighborSet w => z.val.val) eq))
    have bound := Nat.card_le_card_of_injective send inj
    have smaller := low w
    omega

#print axioms no_cross_after_tips
#print axioms actual_stage_exposure_transfer
#print axioms original_cap_after_joining_first_stage
end JSP452Audit.StarHost.NinePortRegion
