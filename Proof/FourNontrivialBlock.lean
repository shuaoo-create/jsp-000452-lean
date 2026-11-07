import FourSelectedBudget
import FourOriginalRoots
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Specialization for degree four: select and cover both possible extra full roots. -/
theorem four_zero_reserve_has_nontrivial_block (Q : SimpleGraph X) (I : Set X)
    (conn : Q.Connected) (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (three : 3≤I.ncard)
    (reg : ∀x,Nat.card (Q.neighborSet x)=4) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q 4=0) (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ)) (gap : N.vertsᶜ.ncard+1=I.ncard)
    (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (clZ : (Q.induce Iᶜ).IsClique (zeroMateRegion (Q.induce Iᶜ) N)) :
    ∃w,w∉N.verts ∧ 3≤(mateBlock (Q.induce Iᶜ) N w).ncard := by
  classical
  by_contra! small
  let H := Q.induce Iᶜ
  let W : Set X := Subtype.val '' N.vertsᶜ
  let Z : Set X := Subtype.val '' zeroMateRegion H N
  obtain ⟨same,size⟩ := singleton_branch_zero_size Q I ind largest 4 (by decide) reg N hm max gap
    noEx small clZ
  have counts := zero_clique_root_degrees Q I 4 reg N same size clZ
  have iw : Disjoint I W := by
    apply Set.disjoint_left.mpr
    rintro _ h ⟨w,hw,rfl⟩
    exact w.property h
  have iz : Disjoint I Z := by
    apply Set.disjoint_left.mpr
    rintro _ h ⟨z,hz,rfl⟩
    exact z.property h
  have wz : Disjoint W Z := by
    apply Set.disjoint_image_of_injective Subtype.val_injective
    rw [←same]
    exact disjoint_compl_left
  have cover : I∪W∪Z=Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases inside : x∈I
    · exact Or.inl (Or.inl inside)
    · let y : ↥(Iᶜ : Set X) := ⟨x,inside⟩
      by_cases used : y∈N.verts
      · exact Or.inr ⟨y,(show y∈zeroMateRegion H N by rw [←same];exact used),rfl⟩
      · exact Or.inl (Or.inr ⟨y,used,rfl⟩)
  have sizeZ : Z.ncard=4 := by
    change (Subtype.val '' zeroMateRegion H N).ncard=4
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,←same,size]
  have cl : Q.IsClique Z := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ ne
    exact clZ ha hb (fun eq => ne (congrArg Subtype.val eq))
  have wNeighbors (w : X) (hw : w∈W) : Q.neighborSet w⊆I := by
    obtain ⟨u,hu,eq⟩ := hw
    subst w
    intro x adj
    by_contra xi
    let b : ↥(Iᶜ : Set X) := ⟨x,xi⟩
    have edge : H.Adj u b := adj
    have used := missed_neighbors_subset H N hm max hu edge
    have bz : b∈zeroMateRegion H N := by rwa [←same]
    obtain ⟨_,_,away,_⟩ := bz
    exact away u hu edge.symm
  obtain ⟨i,z,z₀,a,b,p,q,zi,zz,ab,ia,ib,pi,qi,pq,ap,bq,load⟩ :=
    actual_four_matched_labels Q I W Z conn ind (by omega) iz wz cover sizeZ reg
      (fun x h => (counts x h).1) (fun x h => (counts x h).2) wNeighbors
  have budget := four_selected_cut_budget Q I W Z reg ind cl iw iz wz cover sizeZ
    i z z₀ a b zi zz ab ia ib p q pi qi pq ap bq load
  have wcard : W.ncard=N.vertsᶜ.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  let _ : Nonempty X := conn.nonempty
  have cost := independent_layer_lower Q 3 reg crit I (Set.nonempty_of_ncard_ne_zero (by omega))
    ind 2 (by decide)
  change I.ncard+deletionBudget (Q.induce Iᶜ) 3≤baseReserve Q 4+deletionBudget Q 3 at cost
  rw [zero] at cost
  omega

#print axioms four_zero_reserve_has_nontrivial_block
end JSP452Audit.StarHost
