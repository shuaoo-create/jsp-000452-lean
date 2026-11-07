import MateClasses
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The residual order splits exactly into the sizes of the genuine pointed
blocks, the zero region and the exceptional endpoints, with no duplicates. -/
theorem residual_mate_partition_order (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) :
    Nat.card X = (∑ᶠ w : ↥(N.vertsᶜ),(mateBlock H N w.val).ncard) +
      (zeroMateRegion H N).ncard+(exceptionalMateRegion H N).ncard := by
  classical
  let T (w : ↥(N.vertsᶜ)) := mateBlock H N w.val
  let U : Set X := ⋃ w : ↥(N.vertsᶜ),T w
  have separate : Pairwise (Function.onFun Disjoint T) := by
    intro w u ne
    exact different_mate_blocks_disjoint H N hm max w u w.property u.property
      (fun eq => ne (Subtype.ext eq))
  have countU : U.ncard = ∑ᶠ w : ↥(N.vertsᶜ),(mateBlock H N w.val).ncard :=
    Set.ncard_iUnion_of_finite (fun i => Set.toFinite (T i)) separate
  have uz : Disjoint U (zeroMateRegion H N) := by
    apply Set.disjoint_left.mpr
    intro x hx hz
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (mate_block_disjoint_zero H N hm w w.property) hw hz
  have rest : Disjoint (U∪zeroMateRegion H N) (exceptionalMateRegion H N) := by
    apply Set.disjoint_left.mpr
    rintro x (hx|hz) he
    · obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (mate_block_disjoint_exceptional H N hm w w.property) hw he
    · exact Set.disjoint_left.mp (zero_region_disjoint_exceptional H N hm) hz he
  have all : (U∪zeroMateRegion H N)∪exceptionalMateRegion H N=Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases mate_classes_cover H N hm x with ⟨w,hw,b⟩|z|e
    · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨⟨w,hw⟩,b⟩))
    · exact Or.inl (Or.inr z)
    · exact Or.inr e
  calc
    Nat.card X = ((U∪zeroMateRegion H N)∪exceptionalMateRegion H N).ncard := by rw [all,Set.ncard_univ]
    _ = _ := by rw [Set.ncard_union_eq rest,Set.ncard_union_eq uz,countU]

/-- Full original-label count for the actual near-perfect decomposition.
The exceptional term has cardinal zero or two. -/
theorem original_mate_partition_order (Q : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q D=0) (I : Set X) (ind : Q.IsIndepSet I)
    (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (v : X) (vi : v∈I) (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x|x≠v}) :
    let H := Q.induce Iᶜ
    let N := restrictedOutsideMatching Q I M
    let E := (exceptionalMateRegion H N).ncard
    Nat.card X = I.ncard+(∑ᶠ w : ↥(N.vertsᶜ),(mateBlock H N w.val).ncard) +
      (zeroMateRegion H N).ncard + E ∧ (E=0 ∨ E=2) := by
  intro H N E
  obtain ⟨matchN,rank,clique⟩ := residual_mate_clique Q D pos reg crit zero I ind max v vi M hm expose
  have card := residual_mate_partition_order H N matchN rank
  have total := Set.ncard_add_ncard_compl I
  rw [Nat.card_coe_set_eq] at card
  refine ⟨by omega,?_⟩
  rcases exceptional_region_empty_or_pair H N matchN
      (fun _ _ a b => heavy_endpoint_unique H N matchN rank clique a b) with empty|⟨x,y,_,ne,pair⟩
  · left; change (exceptionalMateRegion H N).ncard=0; rw [empty,Set.ncard_empty]
  · right; change (exceptionalMateRegion H N).ncard=2; rw [pair,Set.ncard_pair ne]

#print axioms original_mate_partition_order
end JSP452Audit.StarHost
