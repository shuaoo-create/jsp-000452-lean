import ProtectedBudgetSplit
import OneLayerPaysPortDeficit
import TightDeletesRank

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Extend an already repaired deletion cut. Only genuinely new labels are charged,
and the layer-zero certificate survives by induced embedding. -/
theorem extend_repaired_cut {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (I0 P : Set X) (ρ m : ℕ)
    (zero : deletionBudget (G.induce I0ᶜ) D = 0)
    (rank : matchingEdges G ≤ matchingEdges (G.induce I0ᶜ)+m)
    (size : I0.ncard=ρ+2*m) :
    deletionBudget (G.induce (I0∪P)ᶜ) D=0 ∧
    matchingEdges G ≤ matchingEdges (G.induce (I0∪P)ᶜ)+m+(P\I0).ncard ∧
    (I0∪P).ncard=ρ+(m+(P\I0).ncard)+m := by
  let Z : Set ↥I0ᶜ := {x | x.val∈P}
  have image : Subtype.val '' Z=P\I0 := by
    ext x
    exact ⟨fun ⟨z,h,eq⟩ => eq ▸ (show z.val∈P\I0 from ⟨h,z.property⟩),
      fun h => ⟨⟨x,h.2⟩,h.1,rfl⟩⟩
  have cost : Z.ncard=(P\I0).ncard := by
    rw [← image,Set.ncard_image_of_injective _ Subtype.val_injective]
  have union : outerCut I0 Z=I0∪P := by
    rw [outerCut,image]
    ext x; simp only [Set.mem_union,Set.mem_sdiff]; tauto
  have count := outerCut_ncard I0 Z
  rw [union,cost] at count
  have next := matching_rank_le_cut_add (G.induce I0ᶜ) Z
  rw [rank_eq_of_graph_iso (nestedCutIso G I0 Z),union,cost] at next
  let e : G.induce (I0∪P)ᶜ ↪g G.induce I0ᶜ := {
    toFun := fun x => ⟨x.val,fun h => x.property (Or.inl h)⟩
    inj' := fun _ _ eq => Subtype.ext (congrArg (fun z : ↥I0ᶜ => z.val) eq)
    map_rel_iff' := Iff.rfl }
  have le := deletionBudget_mono_embedding e D
  exact ⟨by omega,by omega,by omega⟩

/-- A paid below-top saving on the enlarged independent cut gives the full reserve bound. -/
theorem extended_repaired_cut_pays {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) (large : 2≤D)
    (I0 P : Set X) (m h : ℕ)
    (zero : deletionBudget (G.induce I0ᶜ) D=0)
    (rank : matchingEdges G ≤ matchingEdges (G.induce I0ᶜ)+m)
    (size : I0.ncard=minimumExposure G D+2*m)
    (ind : G.IsIndepSet (I0∪P)) (full : ∀ x∈I0∪P, Nat.card (G.neighborSet x)=D)
    (enough : deletionBudget G D≤m+h) (saving : h≤savedAt G (I0∪P) (D-1)) :
    baseReserve (G.induce (I0∪P)ᶜ) D+minimumExposure G D≤baseReserve G D := by
  obtain ⟨_,newRank,newSize⟩ := extend_repaired_cut G D I0 P _ m zero rank size
  apply independent_cut_one_layer_pays G D large (I0∪P) ind full (m+(P\I0).ncard) m h newSize _ enough saving
  omega

#print axioms extend_repaired_cut
#print axioms extended_repaired_cut_pays
end JSP452Audit.StarHost
