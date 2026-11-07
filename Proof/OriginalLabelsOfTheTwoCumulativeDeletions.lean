import ExposurePricesAcrossTwoRealDegreeDrops
open private JSP452Audit.StarHost.degree_sum_left JSP452Audit.StarHost.degree_sum_right from ExposureComponentSum
namespace JSP452Audit.StarHost
open SimpleGraph
universe u v

theorem degree_cap_along_copy {X : Type u} {Y : Type v} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (f : G.Copy H) (D : ℕ)
    (cap : ∀v,Nat.card (H.neighborSet v)≤D) : ∀x,Nat.card (G.neighborSet x)≤D := by
  intro x
  let send (y : G.neighborSet x) : H.neighborSet (f x) := ⟨f y.val,f.toHom.map_adj y.property⟩
  have inj : Function.Injective send := fun _ _ eq => Subtype.ext (f.injective (congrArg Subtype.val eq))
  exact (Nat.card_le_card_of_injective send inj).trans (cap (f x))

theorem cap_on_sum_after_relabeling {X Y Z : Type*} [Finite X] [Finite Y] [Finite Z]
    {G : SimpleGraph X} {H : SimpleGraph Y} {K : SimpleGraph Z} (f : G⊕g H ≃g K) (D : ℕ)
    (left : ∀v,Nat.card (G.neighborSet v)≤D) (right : ∀v,Nat.card (H.neighborSet v)≤D) :
    ∀v,Nat.card (K.neighborSet v)≤D := by
  apply degree_cap_along_copy f.symm.toCopy D
  rintro (x|y)
  · rw [JSP452Audit.StarHost.degree_sum_left];exact left x
  · rw [JSP452Audit.StarHost.degree_sum_right];exact right y

/-- The labels in an induced region after deleting original images of
selected vertices of that same region. -/
noncomputable def strip_inside_labels {X : Type*} (G : SimpleGraph X) (V : Set X) (J : Set V) :
    (G.induce V).induce Jᶜ ≃g G.induce (V\Subtype.val '' J) := by
  have eq : Jᶜ={x : V | x.val∈V\Subtype.val '' J} := by
    ext x
    constructor
    · intro h;exact ⟨x.property,fun ⟨y,hy,e⟩ => h ((Subtype.ext e : y=x) ▸ hy)⟩
    · intro h j;exact h.2 ⟨x,j,rfl⟩
  rw [eq];exact original_induced_subset_iso G V _ Set.sdiff_subset

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)
abbrev outer (B : Set X) := (R.chosen∪B)ᶜ

noncomputable def split_after_original_deletions (I B : Set X) (inside : I⊆R.chosen) (tips : R.tips⊆I)
    (apart : Disjoint B R.chosen) :
    (G.induce (R.chosen\I))⊕g(G.induce (R.outer B)) ≃g G.induce (I∪B)ᶜ := by
  have cover : (R.chosen\I)∪R.outer B=(I∪B)ᶜ := by
    ext x
    constructor
    · rintro (w|o)
      · exact fun h => h.elim w.2 (fun b => Set.disjoint_left.mp apart b w.1)
      · exact fun h => h.elim (fun i => o (Or.inl (inside i))) (fun b => o (Or.inr b))
    · intro h;by_cases w : x∈R.chosen
      · exact Or.inl ⟨w,fun i => h (Or.inl i)⟩
      · exact Or.inr (fun z => z.elim w (fun b => h (Or.inr b)))
  have dis : Disjoint (R.chosen\I) (R.outer B) := Set.disjoint_left.mpr (fun _ w o => o (Or.inl w.1))
  exact regionSumIso G _ _ _ cover dis (fun x xin y yin => R.no_cross_after_tips I B tips
    ⟨xin.1,fun h => h.elim xin.2 (fun b => Set.disjoint_left.mp apart b xin.1)⟩ (fun h => yin (Or.inl h)))

#print axioms split_after_original_deletions
end NinePortRegion
#print axioms degree_cap_along_copy
#print axioms cap_on_sum_after_relabeling
#print axioms strip_inside_labels
end JSP452Audit.StarHost
