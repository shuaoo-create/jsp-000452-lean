import OddCriticalComponentFamiliesOnActualDisjointSums
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def sumLabels {X Y:Type u} (A:Set X) (B:Set Y) : Set (X⊕Y) := Sum.elim (fun x => x∈A) (fun y => y∈B)

def sumLabelEquiv {X Y:Type u} (A:Set X) (B:Set Y) : ↥A⊕↥B ≃ ↥(sumLabels A B) where
  toFun := Sum.elim (fun x => ⟨Sum.inl x.val,x.property⟩) (fun y => ⟨Sum.inr y.val,y.property⟩)
  invFun := fun ⟨z,hz⟩ => match z with | Sum.inl x => Sum.inl ⟨x,hz⟩ | Sum.inr y => Sum.inr ⟨y,hz⟩
  left_inv := by rintro (x|y) <;> rfl
  right_inv := by rintro ⟨(x|y),_⟩ <;> rfl

def inducedSumLabelsIso {X Y:Type u} (G:SimpleGraph X) (H:SimpleGraph Y) (A:Set X) (B:Set Y) :
    (G.induce A⊕g H.induce B) ≃g (G⊕g H).induce (sumLabels A B) where
  toEquiv := sumLabelEquiv A B
  map_rel_iff' := by rintro (x|x) (y|y) <;> rfl

theorem sum_labels_count {X Y:Type u} [Finite X] [Finite Y] (A:Set X) (B:Set Y) :
    (sumLabels A B).ncard=A.ncard+B.ncard :=
  (Nat.card_congr (sumLabelEquiv A B)).symm.trans Nat.card_sum

theorem sum_labels_rank {X Y:Type u} [Finite X] [Finite Y] (G:SimpleGraph X) (H:SimpleGraph Y) (A:Set X) (B:Set Y) :
    matchingEdges ((G⊕g H).induce (sumLabels A B))=matchingEdges (G.induce A)+matchingEdges (H.induce B) := by
  rw [←rank_eq_of_graph_iso (inducedSumLabelsIso G H A B),matchingEdges_sumGraph]

theorem sum_labels_original_degrees {X Y:Type u} [Finite X] [Finite Y] (G:SimpleGraph X) (H:SimpleGraph Y) (A:Set X) (B:Set Y) :
    originalDegreeSum (G⊕g H) (sumLabels A B)=originalDegreeSum G A+originalDegreeSum H B := by
  classical
  let _ := Fintype.ofFinite ↥A
  let _ := Fintype.ofFinite ↥B
  let _ := Fintype.ofFinite ↥(sumLabels A B)
  have expand {Z:Type u} [Finite Z] (K:SimpleGraph Z) (U:Set Z) [Fintype U] :
      originalDegreeSum K U=∑x:↥U,(K.neighborSet x.val).ncard :=
    Finset.sum_subtype U.toFinite.toFinset (fun _ => U.toFinite.mem_toFinset) _
  rw [expand,expand G,expand H]
  let f (z:↥(sumLabels A B)) := ((G⊕g H).neighborSet z.val).ncard
  have eq := Fintype.sum_equiv (sumLabelEquiv A B) (fun z => f (sumLabelEquiv A B z)) f (fun _ => rfl)
  change (∑z,f z)=_
  rw [←eq,Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl;intro x _
    change ((G⊕g H).neighborSet (Sum.inl x.val)).ncard=_
    rw [neighborSet_sum_inl,Set.ncard_image_of_injective _ Sum.inl_injective]
  · apply Finset.sum_congr rfl;intro y _
    change ((G⊕g H).neighborSet (Sum.inr y.val)).ncard=_
    rw [neighborSet_sum_inr,Set.ncard_image_of_injective _ Sum.inr_injective]
#print axioms sum_labels_count
#print axioms sum_labels_rank
#print axioms sum_labels_original_degrees
end JSP452Audit.StarHost
