import ClosedUnionBarrierPieces
namespace JSP452Audit.StarHost
open SimpleGraph

theorem ordinary_region_covers_closed_full_set {X : Type*} [Finite X] (G : SimpleGraph X)
    (D : ℕ) (U : Set X) (closed : ∀v∈U,∀w,G.Adj v w → w∈U)
    (full : ∀v∈U,Nat.card (G.neighborSet v)=D) :
    ∃K:DegreeRegion G D,U⊆K.core∪K.roots := by
  obtain ⟨B⟩ := degreeRegion_exists G D
  let S := B.barrier
  let T := B.pieces
  let W := T∪insideBarrierPieces G S U
  let N := rootNeighbors (rootIncidence G S)
  obtain ⟨A,_⟩ := (allocation_exposure_exact G S B.tight B.critical D).2
  have fullW : W⊆{c | allFullComponent G S D c} := by
    intro c mem
    rcases mem with old|inside
    · exact B.full old
    · exact fun z => full z.val.val (inside z)
  have old : T⊆W := Set.subset_union_left
  have roots : N T⊆N W := by
    rintro a ⟨c,member,link⟩
    exact ⟨c,old member,link⟩
  have upper := (full_component_deficiency G S B.tight B.critical D).1 W fullW
  have diff := augment_root_count G S U closed A T
  change (N W \ N T).ncard≤(W \ T).ncard at diff
  have pieces := Set.ncard_sdiff_add_ncard_of_subset old
  have ports := Set.ncard_sdiff_add_ncard_of_subset roots
  have earlier : T.ncard=(N T).ncard+minimumExposure G D := B.balanced
  have balance : W.ncard=(N W).ncard+minimumExposure G D := by
    change W.ncard≤(N W).ncard+minimumExposure G D at upper
    clear * - upper diff pieces ports earlier
    omega
  let K : DegreeRegion G D := ⟨S,W,B.tight,B.critical,fullW,balance⟩
  refine ⟨K,?_⟩
  intro v hv
  by_cases barrier : v∈S
  · let a : ↥S := ⟨v,barrier⟩
    obtain ⟨z,link⟩ := A.link a
    have inside := inside_of_touching G S U closed (A.place a) z (closed v hv z.val.val link)
    exact Or.inr ⟨a,⟨A.place a,Or.inr inside,z,link⟩,rfl⟩
  · let z : ↥(Sᶜ : Set X) := ⟨v,barrier⟩
    let c := (G.induce Sᶜ).connectedComponentMk z
    have inside := inside_of_touching G S U closed c ⟨z,rfl⟩ hv
    exact Or.inl ⟨z,rfl,Or.inr inside⟩

#print axioms ordinary_region_covers_closed_full_set
end JSP452Audit.StarHost
