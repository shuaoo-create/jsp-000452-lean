import HighStarCover
import ForcingHost

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

abbrev outsideSetEmbed (W : Set X) : ↥(Wᶜ : Set X) ↪ X :=
  Function.Embedding.subtype (· ∈ Wᶜ)

/-- Keep the old red graph on the complement of W. Color all original edges
touching A red; the remaining original edges touching W are blue. -/
def setRestoreRed (G : SimpleGraph X) (W A : Set X) (F : SimpleGraph ↥(Wᶜ : Set X)) :
    SimpleGraph X :=
  F.map (outsideSetEmbed W) ⊔ (G ⊓ fromRel (fun x y => x ∈ A ∨ y ∈ A))

theorem setRestoreRed_le (G : SimpleGraph X) (W A : Set X) (F : SimpleGraph ↥(Wᶜ : Set X))
    (sub : F ≤ G.induce Wᶜ) : setRestoreRed G W A F ≤ G :=
  sup_le ((SimpleGraph.map_le_iff_le_comap _ _ _).mpr sub) inf_le_left

theorem setRestoreRed_induce (G : SimpleGraph X) (W A : Set X) (hA : A ⊆ W)
    (F : SimpleGraph ↥(Wᶜ : Set X)) : (setRestoreRed G W A F).induce Wᶜ = F := by
  ext x y
  constructor
  · rintro (old | touch)
    · exact SimpleGraph.map_adj_apply.mp old
    · have awayX : x.val ∉ A := fun h => x.property (hA h)
      have awayY : y.val ∉ A := fun h => y.property (hA h)
      exact False.elim (touch.2.2.elim (·.elim awayX awayY) (·.elim awayY awayX))
  · intro edge
    exact Or.inl (SimpleGraph.map_adj_apply.mpr edge)

theorem set_restore_lift_cap (W : Set X) (F : SimpleGraph ↥(Wᶜ : Set X)) (p : ℕ)
    (cap : ∀ x, Nat.card (F.neighborSet x) ≤ p) :
    ∀ x, Nat.card ((F.map (outsideSetEmbed W)).neighborSet x) ≤ p := by
  classical
  intro x
  by_cases inW : x ∈ W
  · have empty : (F.map (outsideSetEmbed W)).neighborSet x = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y edge
      obtain ⟨a,b,_,ha,_⟩ := (SimpleGraph.map_adj _ _ _ _).mp edge
      have same : a.val = x := ha
      exact a.property (same.symm ▸ inW)
    rw [Nat.card_coe_set_eq,empty,Set.ncard_empty]
    exact Nat.zero_le _
  · let z : ↥(Wᶜ : Set X) := ⟨x,inW⟩
    change ((F.map (outsideSetEmbed W)).neighborSet (outsideSetEmbed W z)).ncard ≤ p
    rw [SimpleGraph.neighborSet_map,Set.ncard_image_of_injective _ (outsideSetEmbed W).injective]
    exact cap z

/-- Each red edge outside A and each blue edge outside B already belongs to
its original lifted color on the complement of W. -/
theorem set_restore_edge_covers (G : SimpleGraph X) (W A B : Set X) (cover : W = A ∪ B)
    (F : SimpleGraph ↥(Wᶜ : Set X)) :
    (∀ ⦃x y⦄, (setRestoreRed G W A F).Adj x y →
      x ∈ A ∨ y ∈ A ∨ (F.map (outsideSetEmbed W)).Adj x y) ∧
    (∀ ⦃x y⦄, (G \ setRestoreRed G W A F).Adj x y →
      x ∈ B ∨ y ∈ B ∨ (((G.induce Wᶜ) \ F).map (outsideSetEmbed W)).Adj x y) := by
  classical
  constructor
  · intro x y edge
    rcases edge with old | new
    · exact Or.inr (Or.inr old)
    · exact new.2.2.elim (·.elim Or.inl (fun h => Or.inr (Or.inl h)))
        (·.elim (fun h => Or.inr (Or.inl h)) Or.inl)
  · intro x y edge
    by_cases xb : x ∈ B
    · exact Or.inl xb
    by_cases yb : y ∈ B
    · exact Or.inr (Or.inl yb)
    have xa : x ∉ A := fun ha => edge.2 (Or.inr ⟨edge.1,edge.1.ne,Or.inl (Or.inl ha)⟩)
    have ya : y ∉ A := fun ha => edge.2 (Or.inr ⟨edge.1,edge.1.ne,Or.inl (Or.inr ha)⟩)
    have xw : x ∉ W := by rw [cover]; exact fun hx => hx.elim xa xb
    have yw : y ∉ W := by rw [cover]; exact fun hy => hy.elim ya yb
    let u : ↥(Wᶜ : Set X) := ⟨x,xw⟩
    let v : ↥(Wᶜ : Set X) := ⟨y,yw⟩
    have noRed : ¬ F.Adj u v := fun f => edge.2 (Or.inl (SimpleGraph.map_adj_apply.mpr f))
    exact Or.inr (Or.inr ((SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,⟨edge.1,noRed⟩,rfl,rfl⟩))

/-- Both inequalities concern copies in the same restored coloring. The list
indices and sizes can be arbitrary, with p or q equal to zero allowed. -/
theorem set_restore_large_counts {I J : Type*} [Finite X] [Fintype I] [Fintype J]
    (G : SimpleGraph X) (W A B : Set X) (cover : W = A ∪ B)
    (F : SimpleGraph ↥(Wᶜ : Set X)) (sub : F ≤ G.induce Wᶜ) {p q : ℕ}
    (redCap : ∀ x, Nat.card (F.neighborSet x) ≤ p)
    (blueCap : ∀ x, Nat.card ((G.induce Wᶜ \ F).neighborSet x) ≤ q)
    (n : I → ℕ) (m : J → ℕ) :
    ∃ R ≤ G, R.induce Wᶜ = F ∧
      ((forest n).IsContained R →
        (Finset.univ.filter (fun i => p+1 ≤ n i)).card ≤ A.ncard) ∧
      ((forest m).IsContained (G \ R) →
        (Finset.univ.filter (fun j => q+1 ≤ m j)).card ≤ B.ncard) := by
  have hA : A ⊆ W := cover ▸ Set.subset_union_left
  obtain ⟨redEdges,blueEdges⟩ := set_restore_edge_covers G W A B cover F
  exact ⟨setRestoreRed G W A F,setRestoreRed_le G W A F sub,setRestoreRed_induce G W A hA F,
    count_large_of_edge_cover _ _ A p n redEdges (set_restore_lift_cap W F p redCap),
    count_large_of_edge_cover _ _ B q m blueEdges (set_restore_lift_cap W _ q blueCap)⟩

#print axioms set_restore_edge_covers
#print axioms set_restore_large_counts
end JSP452Audit.StarHost
