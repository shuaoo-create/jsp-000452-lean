import TutteBergeExact
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}
/-- Two consecutive cuts expressed using the original vertex labels. -/
def outerCut (S : Set X) (Z : Set ↥(Sᶜ : Set X)) : Set X := S ∪ Subtype.val '' Z

def nestedCutIso (G : SimpleGraph X) (S : Set X) (Z : Set ↥(Sᶜ : Set X)) :
    (G.induce Sᶜ).induce Zᶜ ≃g G.induce (outerCut S Z)ᶜ where
  toFun w := ⟨w.val.val, by
    rintro (ins | ⟨z,hz,he⟩)
    · exact w.val.property ins
    · exact w.property ((Subtype.ext he : z=w.val) ▸ hz)⟩
  invFun x := by
    let w : ↥(Sᶜ : Set X) := ⟨x.val,fun h => x.property (Or.inl h)⟩
    exact ⟨w,fun h => x.property (Or.inr ⟨w,h,rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem outerCut_ncard [Finite X] (S : Set X) (Z : Set ↥(Sᶜ : Set X)) :
    (outerCut S Z).ncard = S.ncard + Z.ncard := by
  have dis : Disjoint S (Subtype.val '' Z) := Set.disjoint_left.mpr (by
    rintro x inS ⟨z,_,rfl⟩
    exact z.property inS)
  rw [outerCut,Set.ncard_union_eq dis,Set.ncard_image_of_injective _ Subtype.val_injective]

theorem outerCut_strict (S : Set X) (Z : Set ↥(Sᶜ : Set X)) (present : Z.Nonempty) :
    S ⊂ outerCut S Z := by
  refine ⟨Set.subset_union_left,?_⟩
  obtain ⟨z,hz⟩ := present
  exact fun back => z.property (back (Or.inr ⟨z,hz,rfl⟩))

#print axioms nestedCutIso
#print axioms outerCut_ncard
#print axioms outerCut_strict
end JSP452Audit.StarHost