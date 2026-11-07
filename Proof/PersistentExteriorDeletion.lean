import ProtectedCoreRankAndExposure
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem disjoint_induced_matching_ranks (G : SimpleGraph X) (U P Q : Set X)
    (pU : P⊆U) (qU : Q⊆U) (apart : Disjoint P Q) :
    matchingEdges (G.induce P)+matchingEdges (G.induce Q)≤matchingEdges (G.induce U) := by
  let join : ↥P⊕↥Q → U := Sum.elim (fun p => ⟨p.val,pU p.property⟩) (fun q => ⟨q.val,qU q.property⟩)
  have inj : Function.Injective join := by
    rintro (a|b) (c|d) eq
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun z:U => z.val) eq))
    · exact (apart.ne_of_mem a.property d.property (congrArg (fun z:U => z.val) eq)).elim
    · exact (apart.ne_of_mem c.property b.property (congrArg (fun z:U => z.val) eq).symm).elim
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun z:U => z.val) eq))
  have map {a b : ↥P⊕↥Q} (edge : (G.induce P ⊕g G.induce Q).Adj a b) :
      (G.induce U).Adj (join a) (join b) := by
    rcases a with a|a <;> rcases b with b|b
    · exact edge
    · exact (not_adj_sum_inl_inr _ _ edge).elim
    · exact (not_adj_sum_inl_inr _ _ edge.symm).elim
    · exact edge
  let e : (G.induce P ⊕g G.induce Q).Copy (G.induce U) := ⟨⟨join,map⟩,inj⟩
  simpa only [matchingEdges_sumGraph] using rank_le_of_copy e

/-- Delete any set from the actual exterior. The old exposure persists,
and the unchanged core-plus-roots matching can be realized disjointly
from any matching in the surviving exterior. -/
theorem ordinary_region_after_exterior_deletions (G : SimpleGraph X) {D : ℕ} (K : DegreeRegion G D)
    (W : Set X) (ext : W⊆K.rest) :
    minimumExposure G D≤minimumExposure (G.induce Wᶜ) D ∧
      K.roots.ncard+matchingEdges (G.induce K.core)+matchingEdges (G.induce (K.rest\W))≤
        matchingEdges (G.induce Wᶜ) := by
  obtain ⟨ap,ab,pb,_⟩ := region_partition G K.barrier K.pieces
  change Disjoint K.roots K.core at ap
  change Disjoint K.roots K.rest at ab
  change Disjoint K.core K.rest at pb
  have pU : K.core⊆Wᶜ := fun v hp w => Set.disjoint_left.mp pb hp (ext w)
  have aU : K.roots⊆Wᶜ := fun v ha w => Set.disjoint_left.mp ab ha (ext w)
  let P : Set ↥(Wᶜ : Set X) := {v | v.val∈K.core}
  let A : Set ↥(Wᶜ : Set X) := {v | v.val∈K.roots}
  let H := G.induce Wᶜ
  have apart : Disjoint P A := Set.disjoint_left.mpr (fun _ p a => Set.disjoint_left.mp ap a p)
  have outside (v : ↥(Wᶜ : Set X)) (hp:v∈P) (u : ↥(Wᶜ : Set X)) (e:H.Adj v u) (away:u∉P) : u∈A :=
    (regionCore_neighbor G K.barrier K.pieces hp e).resolve_right away
  have full (v : ↥(Wᶜ : Set X)) (hp:v∈P) : Nat.card (H.neighborSet v)=D := by
    have inc : G.neighborSet v.val⊆Wᶜ := by
      intro w edge hw
      rcases regionCore_neighbor G K.barrier K.pieces hp edge with root|core
      · exact aU root hw
      · exact pU core hw
    rw [induced_degree_intersection,Set.inter_eq_left.mpr inc,←Nat.card_coe_set_eq]
    exact regionCore_full_degree G K.barrier K.pieces D K.full hp
  have pcard : P.ncard=K.core.ncard := subset_card_on_surviving_labels Wᶜ K.core pU
  have acard : A.ncard=K.roots.ncard := subset_card_on_surviving_labels Wᶜ K.roots aU
  have rank : matchingEdges (H.induce P)=matchingEdges (G.induce K.core) :=
    rank_eq_of_graph_iso (original_induced_subset_iso G Wᶜ K.core pU)
  constructor
  · apply protected_full_core_exposure H P A apart outside D _ full
    rw [pcard,acard,rank];exact K.core_order
  · have lower := disjoint_induced_matching_ranks G Wᶜ (K.core∪K.roots) (K.rest\W)
      (Set.union_subset pU aU) (fun _ h => h.2)
      ((Set.disjoint_union_left.mpr ⟨pb,ab⟩).mono_right Set.sdiff_subset)
    rw [ordinary_region_internal_root_rank G D K] at lower
    omega

#print axioms disjoint_induced_matching_ranks
#print axioms ordinary_region_after_exterior_deletions
end JSP452Audit.StarHost
