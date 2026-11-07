import DetachedPreferredCount
import ExposableCross
import BlockWithZeroRegion

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A crossing between the preferred union (including the zero region) and a
different block cannot have endpoints exposable on both sides. -/
theorem preferred_union_exposed_no_cross (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard = matchingEdges H)
    {w u : X} (hw : w ∉ N.verts) (hu : u ∉ N.verts) (ne : w ≠ u)
    (x : ↥(mateBlock H N w ∪ zeroMateRegion H N)) (y : mateBlock H N u)
    (ex : ExposablePoint (H.induce (mateBlock H N w ∪ zeroMateRegion H N)) x)
    (ey : ExposablePoint (H.induce (mateBlock H N u)) y) :
    ¬ H.Adj x.val y.val := by
  let A := mateBlock H N w ∪ zeroMateRegion H N
  let B := mateBlock H N u
  have apart : Disjoint A B := Set.disjoint_union_left.mpr
    ⟨different_mate_blocks_disjoint H N hm maximum w u hw hu ne,
     (mate_block_disjoint_zero H N hm u hu).symm⟩
  have closed : mateClosed N (A ∪ B) :=
    ((pointed_mate_block_closed H N hm w hw).union (zero_mate_region_closed H N hm)).union
      (pointed_mate_block_closed H N hm u hu)
  have inside : w ∈ A ∪ B := Or.inl (Or.inl (mateBlock_self H N w))
  intro edge
  exact closed_region_with_hole_no_perfect H N hm maximum (A ∪ B) closed w hw inside
    (exposed_cross_perfect_union H A B apart x.property y.property ex ey edge)

/-- In an odd graph with independence number at most two, a vertex whose
deletion leaves a preconnected graph can be the sole uncovered vertex. -/
private theorem exposed_of_preconnected_deletion (G : SimpleGraph X) (v : X)
    (odd : Odd (Nat.card X)) (small : NoIndependentTriple G)
    (conn : (G.induce {x | x ≠ v}).Preconnected) : ExposablePoint G v := by
  apply perfect_of_preconnected_even_no_independent_triple _ conn _ (small.induce _)
  have eq : {x : X | x ≠ v} = ({v} : Set X)ᶜ := by ext; simp
  rw [Nat.card_coe_set_eq, eq, Set.ncard_compl, Set.ncard_singleton, Nat.even_iff]
  have parity := Nat.odd_iff.mp odd
  omega

/-- For each actual crossing to a companion clique, the preferred endpoint
itself disconnects the preferred union when deleted. -/
theorem preferred_cross_forces_cut_at_endpoint (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard = matchingEdges H)
    {w u : X} (hw : w ∉ N.verts) (hu : u ∉ N.verts) (ne : w ≠ u)
    (limit : ∀ S : Set X, H.IsIndepSet S → S.ncard ≤ N.vertsᶜ.ncard + 1)
    (clique : H.IsClique (mateBlock H N u))
    (x : ↥(mateBlock H N w ∪ zeroMateRegion H N)) (y : mateBlock H N u)
    (edge : H.Adj x.val y.val) :
    ¬ ((H.induce (mateBlock H N w ∪ zeroMateRegion H N)).induce {v | v ≠ x}).Preconnected := by
  let A := mateBlock H N w ∪ zeroMateRegion H N
  let B := mateBlock H N u
  have oddA : Odd (Nat.card A) := by
    rw [Nat.card_coe_set_eq]
    exact preferred_region_odd H N hm w hw
  have oddB : Odd (Nat.card B) := by
    rw [Nat.card_coe_set_eq]
    exact mateBlock_odd H N hm u hu
  have critB : PerfectAfterEveryDeletion (H.induce B) := by
    apply critical_of_odd_small_alpha _ oddB
    · intro a b c ab _ _
      exact Or.inl (clique a.property b.property (fun eq => ab (Subtype.ext eq)))
    · intro v a b
      by_cases eq : a = b
      · exact eq ▸ Reachable.refl a
      · have diff : a.val.val ≠ b.val.val := fun h => eq (Subtype.ext (Subtype.ext h))
        exact (show ((H.induce B).induce {z | z ≠ v}).Adj a b from
          clique a.val.property b.val.property diff).reachable
  intro conn
  have ex := exposed_of_preconnected_deletion (H.induce A) x oddA
    (block_with_zero_region_small H N hm maximum w hw limit) conn
  exact preferred_union_exposed_no_cross H N hm maximum hw hu ne x y ex (critB y) edge

#print axioms preferred_union_exposed_no_cross
#print axioms preferred_cross_forces_cut_at_endpoint
end JSP452Audit.StarHost
