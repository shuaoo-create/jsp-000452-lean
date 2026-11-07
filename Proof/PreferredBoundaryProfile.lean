import SmallBlockBoundary
import PreferredMateConnected
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The original independent maximum supplies an external edge at every
vertex of any region in its complement. -/
theorem boundary_at_least_region_order (Q : SimpleGraph X) (I B : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (outside : B⊆Iᶜ) : B.ncard≤crossCount Q B Bᶜ := by
  classical
  let _ := Fintype.ofFinite B
  have pos (b : B) : 1≤(Q.neighborSet b.val∩Bᶜ).ncard := by
    obtain ⟨u,iu,edge⟩ := largest_independent_dominates Q I ind largest b.val (outside b.property)
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨u,edge,fun ub => outside ub iu⟩
  have le := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => pos b)
  rw [crossCount_eq_neighbor_sum]
  simpa [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using le

theorem zero_region_even (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching) :
    Even (zeroMateRegion H N).ncard := by
  let Z := zeroMateRegion H N
  let P : (H.induce Z).Subgraph := {
    verts := Set.univ
    Adj x y := N.Adj x.val y.val
    adj_sub := fun e => N.adj_sub e
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ e => e.symm⟩ }
  have pm : P.IsMatching := by
    intro a _
    obtain ⟨y,ay,ax,byy⟩ := a.property
    let b : Z := ⟨y,⟨a.val,ay.symm,byy,ax⟩⟩
    exact ⟨b,ay,fun z ez => Subtype.ext (hm.eq_of_adj_left ez ay)⟩
  have paired := matching_vertices_eq_twice_edges pm
  change (Set.univ : Set Z).ncard=2*P.edgeSet.ncard at paired
  rw [Set.ncard_univ,Nat.card_coe_set_eq] at paired
  exact ⟨P.edgeSet.ncard,by change Z.ncard=_;omega⟩

theorem preferred_region_odd (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (w : X) (hw : w∉N.verts) :
    Odd (mateBlock H N w∪zeroMateRegion H N).ncard := by
  rw [Set.ncard_union_eq (mate_block_disjoint_zero H N hm w hw)]
  exact (mateBlock_odd H N hm w hw).add_even (zero_region_even H N hm)

theorem original_preferred_region_boundary (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard) (D : ℕ) (six : 6≤D)
    (evenD : Even D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (w : ↥(Iᶜ : Set X)) (hw : w∉N.verts)
    (big : 3≤(mateBlock (Q.induce Iᶜ) N w).ncard) :
    let B := Subtype.val '' (mateBlock (Q.induce Iᶜ) N w∪zeroMateRegion (Q.induce Iᶜ) N)
    (D+1≤B.ncard → D+1≤crossCount Q B Bᶜ) ∧
    (B.ncard≤D-1 → crossCount Q B Bᶜ≤2*D →
      (D=6 ∧ B.ncard=3 ∧ (Q.induce B)ᶜ.edgeSet.ncard=0) ∨
        (B.ncard=D-1 ∧ (Q.induce B)ᶜ.edgeSet.ncard≤1)) := by
  intro B
  let T := mateBlock (Q.induce Iᶜ) N w∪zeroMateRegion (Q.induce Iᶜ) N
  have count : B.ncard=T.ncard := Set.ncard_image_of_injective T Subtype.val_injective
  have outside : B⊆Iᶜ := by rintro _ ⟨x,_,rfl⟩;exact x.property
  have odd := preferred_region_odd (Q.induce Iᶜ) N hm w hw
  have three : 3≤B.ncard := by
    rw [count]; exact big.trans (Set.ncard_le_ncard (show mateBlock (Q.induce Iᶜ) N w⊆T from Set.subset_union_left))
  exact ⟨fun h => h.trans (boundary_at_least_region_order Q I B ind largest outside),
    fun hi cost => low_boundary_small_region Q B D six evenD (count ▸ odd) three hi (fun x _ => reg x) cost⟩

#print axioms original_preferred_region_boundary
end JSP452Audit.StarHost
