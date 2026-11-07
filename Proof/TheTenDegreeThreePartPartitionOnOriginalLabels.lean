import EnlargeTheSupportByTheMatchedPortEndpoints
namespace JSP452Audit.StarHost.TenOuterCut.InnerBarrier
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenOuterCut G} (B:K.InnerBarrier)

def oldRoots : Set X := Subtype.val '' B.roots
def actualRoots : Set X := B.oldRoots∪K.exteriorTargetEnds
def residual : Set X := K.support\B.oldRoots

theorem old_roots_inside : B.oldRoots⊆K.support := by rintro _ ⟨v,_,rfl⟩;exact v.property
theorem original_source_in_roots : K.S⊆B.oldRoots := by
  intro x hx
  let v : ↥K.support := ⟨x,Or.inl (Or.inl hx)⟩
  exact ⟨v,B.contains (show v∈K.sourceInside from hx),rfl⟩
theorem old_root_count : B.oldRoots.ncard=B.roots.ncard := Set.ncard_image_of_injective _ Subtype.val_injective

def residualIso : ((G.induce K.support).induce B.rootsᶜ) ≃g G.induce B.residual where
  toFun x := ⟨x.val.val,x.val.property,by
    rintro ⟨v,hv,eq⟩;exact x.property ((Subtype.ext eq : v=x.val) ▸ hv)⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,fun hx => x.property.2 ⟨⟨x.val,x.property.1⟩,hx,rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem covers_enlarged : B.actualRoots∪B.residual=K.enlargedSupport := by
  ext x
  constructor
  · rintro ((h|h)|h);exact Or.inl (B.old_roots_inside h);exact Or.inr h;exact Or.inl h.1
  · rintro (w|e)
    · by_cases root:x∈B.oldRoots;exact Or.inl (Or.inl root);exact Or.inr ⟨w,root⟩
    · exact Or.inl (Or.inr e)

theorem physical_partition :
    Disjoint B.actualRoots B.residual ∧ Disjoint B.actualRoots K.remainder ∧
      Disjoint B.residual K.remainder ∧ B.actualRoots∪B.residual∪K.remainder=Set.univ ∧
      ∀x∈B.residual,∀y∈K.remainder,¬G.Adj x y := by
  have insideA : B.actualRoots⊆K.enlargedSupport := fun _ h => h.elim (fun a => Or.inl (B.old_roots_inside a)) Or.inr
  have insideR : B.residual⊆K.enlargedSupport := fun _ h => Or.inl h.1
  refine ⟨Set.disjoint_left.mpr (fun x a r => a.elim r.2 (fun e => e.1 r.1)),
    disjoint_compl_right.mono_left insideA,disjoint_compl_right.mono_left insideR,?_,?_⟩
  · rw [B.covers_enlarged];exact Set.union_compl_self _
  · intro x hx y hy adj
    have outside : y∉K.support := fun w => hy (Or.inl w)
    rcases hx.1 with (s|t)|j
    · exact hx.2 (B.original_source_in_roots s)
    · exact hy (Or.inr (show y∈K.exteriorTargetEnds from ⟨outside,x,t,adj⟩))
    · obtain root|inside := regionCore_neighbor G K.roots K.pieces j adj
      · obtain ⟨v,_,rfl⟩ := root;exact outside (Or.inl v.property)
      · exact outside (Or.inr inside)

theorem exact_region_matching_partition (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (best:M.edgeSet.ncard=matchingEdges G) (attained:(exposedFull G M 10).ncard=K.score+2) :
    matchingEdges K.incidentPiece=B.actualRoots.ncard+matchingEdges (G.induce B.residual) ∧
    matchingEdges G=B.actualRoots.ncard+matchingEdges (G.induce B.residual)+matchingEdges (G.induce K.remainder) ∧
    (Set.univ:Set ((G.induce K.support).induce B.rootsᶜ).ConnectedComponent).ncard=
      B.actualRoots.ncard+K.score+2+K.rootDefect K.T := by
  have dis : Disjoint B.oldRoots K.exteriorTargetEnds := K.disjoint_ends.mono_left B.old_roots_inside
  have roots := Set.ncard_union_eq dis
  change B.actualRoots.ncard=B.oldRoots.ncard+K.exteriorTargetEnds.ncard at roots
  rw [B.old_root_count,K.exterior_end_count cap M hm attained] at roots
  obtain ⟨components,rank⟩ := K.inner_barrier_component_account B cap M hm attained
  rw [rank_eq_of_graph_iso B.residualIso] at rank
  have piece := K.incident_piece_rank cap M hm attained
  have split := (K.enlarged_and_remainder_rank cap M hm best attained).2.2
  omega
#print axioms residualIso
#print axioms physical_partition
#print axioms exact_region_matching_partition
end JSP452Audit.StarHost.TenOuterCut.InnerBarrier
