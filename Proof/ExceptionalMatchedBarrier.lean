import NoExceptionPositiveReserve
import ExposableCross
import AlternatingFive
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- An old closed part disjoint from both changed endpoints and the new matched
hole remains closed. This claim uses the actual partner uniqueness in P. -/
private theorem retained_mate_closed (H : SimpleGraph X) (N P : H.Subgraph)
    (hm : N.IsMatching) (hp : P.IsMatching) {w a b : X}
    (supp : P.verts=insert w (N.verts\{b}))
    (keep : ∀{c d : X},N.Adj c d → c∉({a,b} : Set X) → d∉({a,b} : Set X) → P.Adj c d)
    (S : Set X) (old : mateClosed N S) (outside : w∉S)
    (away : Disjoint S ({a,b} : Set X)) : mateClosed P S := by
  intro c d cd hc
  have used := P.edge_vert cd
  rw [supp] at used
  have oldUsed : c∈N.verts := by
    rcases Set.mem_insert_iff.mp used with eq|mem
    · exact False.elim (outside (eq ▸ hc))
    · exact mem.1
  obtain ⟨v,cv,_⟩ := hm oldUsed
  have hv := old cv hc
  have newEdge := keep cv (fun mem => Set.disjoint_left.mp away hc mem)
    (fun mem => Set.disjoint_left.mp away hv mem)
  exact (hp.eq_of_adj_left cd newEdge).symm ▸ hv

theorem odd_clique_exposes_each (H : SimpleGraph X) (C : Set X) (cl : H.IsClique C)
    (odd : Odd C.ncard) : PerfectAfterEveryDeletion (H.induce C) := by
  apply critical_of_odd_small_alpha
  · simpa only [Nat.card_coe_set_eq] using odd
  · intro a b c ab _ _
    exact Or.inl (cl a.property b.property (fun eq => ab (Subtype.ext eq)))
  · intro v a b
    by_cases eq : a=b
    · exact eq ▸ Reachable.refl a
    · have ne : a.val.val≠b.val.val := fun h => eq (Subtype.ext (Subtype.ext h))
      exact (show ((H.induce C).induce {z | z≠v}).Adj a b from cl a.val.property b.val.property ne).reachable

/-- In the original labels, the zero region plus the partner of a heavy
endpoint is an odd clique. No exposable vertex of an ordinary block touches
this clique: moving a different hole to that partner would enlarge a maximum
matching on the union. -/
theorem exceptional_partner_exposure_barrier (H : SimpleGraph X) (N : H.Subgraph)
    (hm : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (anti : H.IsClique (mateAntineighborhood H N.vertsᶜ))
    {a b : X} (heavy : holeHeavy H N a) (ab : N.Adj a b) :
    let K := zeroMateRegion H N ∪ {b}
    H.IsClique K ∧ Odd K.ncard ∧
      ∀j,j∉N.verts → ∀v : mateBlock H N j,ExposablePoint (H.induce (mateBlock H N j)) v →
        ∀z:K,¬H.Adj v.val z.val := by
  intro K
  classical
  let Z := zeroMateRegion H N
  have ae : a∈exceptionalMateRegion H N := ⟨b,ab,Or.inl heavy⟩
  have be : b∈exceptionalMateRegion H N := ⟨a,ab.symm,Or.inr heavy⟩
  have pairSub : ({a,b} : Set X)⊆exceptionalMateRegion H N := by
    rintro v (eq|eq)
    · exact eq.symm ▸ ae
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ be
  have ba := holeHeavy_partner_mem_antineighborhood H N hm maximum heavy ab
  have sub : K⊆mateAntineighborhood H N.vertsᶜ := by
    rintro v (hz|eq)
    · exact zeroMateRegion_subset_anti H N hz
    · exact (Set.mem_singleton_iff.mp eq).symm ▸ ba
  have cl : H.IsClique K := anti.subset sub
  have zDis : Disjoint Z (exceptionalMateRegion H N) := zero_region_disjoint_exceptional H N hm
  have bsub : ({b} : Set X)⊆exceptionalMateRegion H N := Set.singleton_subset_iff.mpr be
  have kodd : Odd K.ncard := by
    change Odd (Z∪{b}).ncard
    rw [Set.ncard_union_eq (zDis.mono_right bsub),Set.ncard_singleton]
    exact Even.add_one (zero_region_even H N hm)
  have critical := odd_clique_exposes_each H K cl kodd
  refine ⟨cl,kodd,?_⟩
  intro j hj v ex z edge
  let T := mateBlock H N j
  have dt := mate_block_disjoint_exceptional H N hm j hj
  have apart : Disjoint T K := Set.disjoint_union_right.mpr
    ⟨mate_block_disjoint_zero H N hm j hj,dt.mono_right bsub⟩
  obtain ⟨w,hw,wa,wj⟩ := holeHeavy_exposed_neighbor_ne H N heavy j
  obtain ⟨M,mm,card,supp,_,keep⟩ := shift_matching_hole H N hm hw ab wa
  have bw : b≠w := fun eq => hw (eq ▸ N.edge_vert ab.symm)
  have bf : b∉M.verts := by simp [supp,bw]
  have wt : w∉T := fun mem => Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N j) mem ⟨hw,by simpa using wj⟩
  have wz : w∉Z := by rintro ⟨v,wv,_,_⟩;exact hw (N.edge_vert wv)
  have ct : mateClosed M T := retained_mate_closed H N M hm mm supp keep T
    (pointed_mate_block_closed H N hm j hj) wt (dt.mono_right pairSub)
  have cz : mateClosed M Z := retained_mate_closed H N M hm mm supp keep Z
    (zero_mate_region_closed H N hm) wz (zDis.mono_right pairSub)
  have cb : mateClosed M ({b}:Set X) := by
    intro u v uv hu
    exact False.elim (bf ((Set.mem_singleton_iff.mp hu) ▸ M.edge_vert uv))
  have ck : mateClosed M K := cz.union cb
  have contradict := closed_region_with_hole_no_perfect H M mm (card.trans maximum) (T∪K) (ct.union ck)
    b bf (Or.inr (Or.inr (Set.mem_singleton b)))
  exact contradict (exposed_cross_perfect_union H T K apart v.property z.property ex (critical z) edge)

#print axioms exceptional_partner_exposure_barrier
end JSP452Audit.StarHost
