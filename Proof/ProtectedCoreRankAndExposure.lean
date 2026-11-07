import ProtectedMatchingCounts
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem full_core_coverage_account (G : SimpleGraph X) (P : Set X) (D : ℕ)
    (full : ∀v∈P,Nat.card (G.neighborSet v)=D) (M : G.Subgraph) :
    P.ncard≤(P∩M.verts).ncard+(exposedFull G M D).ncard := by
  let T := P∩M.verts
  have sub : P\T⊆exposedFull G M D := by
    intro v h;exact ⟨fun hv => h.2 ⟨h.1,hv⟩,full v h.1⟩
  have loss := Set.ncard_sdiff_add_ncard_of_subset (show T⊆P from Set.inter_subset_left)
  have bound := Set.ncard_le_ncard sub
  change P.ncard≤T.ncard+_
  omega

theorem protected_full_core_exposure (G : SimpleGraph X) (P A : Set X) (apart : Disjoint P A)
    (outside : ∀v∈P,∀w,G.Adj v w → w∉P → w∈A) (D ρ : ℕ)
    (full : ∀v∈P,Nat.card (G.neighborSet v)=D)
    (size : P.ncard=2*matchingEdges (G.induce P)+A.ncard+ρ) :
    ρ≤minimumExposure G D := by
  apply (le_minimumExposure_iff G D ρ).mpr
  intro M hm _
  have a := (protected_matching_counts G P A apart outside M hm).1
  have b := full_core_coverage_account G P D full M
  omega

def original_induced_subset_iso (G : SimpleGraph X) (U P : Set X) (inc : P⊆U) :
    ((G.induce U).induce {v : U | v.val∈P}) ≃g G.induce P where
  toFun v := ⟨v.val.val,v.property⟩
  invFun v := ⟨⟨v.val,inc v.property⟩,v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem subset_card_on_surviving_labels (U P : Set X) (inc : P⊆U) :
    ({v:U | v.val∈P} : Set U).ncard=P.ncard := by
  let V : Set U := {v | v.val∈P}
  have image : Subtype.val '' V=P := by
    ext v;exact ⟨fun ⟨x,h,e⟩ => e ▸ h,fun h => ⟨⟨v,inc h⟩,h,rfl⟩⟩
  exact (Set.ncard_image_of_injective V Subtype.val_injective).symm.trans (congrArg Set.ncard image)

theorem matching_rank_with_added_roots (G : SimpleGraph X) (P A : Set X) (apart : Disjoint P A) :
    matchingEdges (G.induce (P∪A))≤matchingEdges (G.induce P)+A.ncard := by
  let U := P∪A
  let R : Set U := {v | v.val∈A}
  have comp : Rᶜ={v : U | v.val∈P} := by
    ext v
    exact ⟨fun no => v.property.resolve_right no,fun hp ha => Set.disjoint_left.mp apart hp ha⟩
  have bound := matching_rank_le_cut_add (G.induce U) R
  have card : R.ncard=A.ncard := subset_card_on_surviving_labels U A Set.subset_union_right
  have eq := rank_eq_of_graph_iso (original_induced_subset_iso G U P Set.subset_union_left)
  rw [card,comp,eq] at bound
  exact bound.trans_eq (Nat.add_comm _ _)

/-- For the actual attaining exposure, the lower coverage account saturates
the genuine protected subgraph on the entire core and its roots. -/
theorem ordinary_region_internal_root_rank (G : SimpleGraph X) (D : ℕ) (K : DegreeRegion G D) :
    matchingEdges (G.induce (K.core∪K.roots))=matchingEdges (G.induce K.core)+K.roots.ncard := by
  let P := K.core
  let A := K.roots
  have apart : Disjoint P A := (region_partition G K.barrier K.pieces).1.symm
  have outside (v:X) (hv:v∈P) (w:X) (e:G.Adj v w) (away:w∉P) : w∈A :=
    (regionCore_neighbor G K.barrier K.pieces hv e).resolve_right away
  obtain ⟨M,hm,_,optimal⟩ := minimumExposure_attained G D
  have full (v:X) (hv:v∈P) : Nat.card (G.neighborSet v)=D :=
    regionCore_full_degree G K.barrier K.pieces D K.full hv
  have covered := full_core_coverage_account G P D full M
  rw [optimal] at covered
  have count := (protected_matching_counts G P A apart outside M hm).2
  have size : P.ncard=2*matchingEdges (G.induce P)+A.ncard+minimumExposure G D := K.core_order
  change matchingEdges (G.induce (P∪A))=matchingEdges (G.induce P)+A.ncard
  exact Nat.le_antisymm (matching_rank_with_added_roots G P A apart) (by omega)

#print axioms full_core_coverage_account
#print axioms protected_full_core_exposure
#print axioms matching_rank_with_added_roots
#print axioms ordinary_region_internal_root_rank
end JSP452Audit.StarHost
