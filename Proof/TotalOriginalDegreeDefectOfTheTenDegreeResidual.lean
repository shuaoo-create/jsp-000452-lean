import TheTenDegreeThreePartPartitionOnOriginalLabels
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem defect_add_disjoint (cap:∀x,Nat.card (G.neighborSet x)≤10) (A B:Set X) (dis:Disjoint A B) :
    K.rootDefect (A∪B)=K.rootDefect A+K.rootDefect B := by
  have a := degree_sum_le_cap G A 10 (fun x _ => cap x)
  have b := degree_sum_le_cap G B 10 (fun x _ => cap x)
  dsimp only [rootDefect];rw [Set.ncard_union_eq dis,original_degree_sum_of_disjoint_union G A B dis];omega

theorem defect_mono (cap:∀x,Nat.card (G.neighborSet x)≤10) {A B:Set X} (sub:A⊆B) : K.rootDefect A≤K.rootDefect B := by
  have dis : Disjoint A (B\A) := Set.disjoint_left.mpr (fun _ a b => b.2 a)
  have un : A∪(B\A)=B := by
    ext x;by_cases hx:x∈A
    · simp [hx,sub hx]
    · simp [hx]
  have fee := K.defect_add_disjoint cap A (B\A) dis
  rw [un] at fee;omega

namespace InnerBarrier
variable {K} (B:K.InnerBarrier)

theorem residual_original_defect (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    K.rootDefect B.residual≤K.rootDefect K.T ∧ K.rootDefect K.T≤2 := by
  let R := B.residual
  have full (x) (hx:x∈R\K.T) : Nat.card (G.neighborSet x)=10 := by
    have member : x∈B.residual := hx.1
    rcases member.1 with (s|t)|j
    · exact (member.2 (B.original_source_in_roots s)).elim
    · exact (hx.2 t).elim
    · exact K.core_is_full cap x j
  have dis : Disjoint (R∩K.T) (R\K.T) := Set.disjoint_left.mpr (fun _ a b => b.2 a.2)
  have un : (R∩K.T)∪(R\K.T)=R := by ext x;simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_sdiff];tauto
  have split := K.defect_add_disjoint cap (R∩K.T) (R\K.T) dis
  rw [un] at split
  have zero : K.rootDefect (R\K.T)=0 := by dsimp only [rootDefect];rw [degree_sum_full G _ 10 full,Nat.sub_self]
  have few := K.defect_mono cap (Set.inter_subset_right (s:=R) (t:=K.T))
  have charge := (K.true_piece_edge_fee cap none).2
  have pos := K.positive
  change K.rootDefect R≤_ ∧ _;omega

theorem residual_order_identity (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (best:M.edgeSet.ncard=matchingEdges G) (attained:(exposedFull G M 10).ncard=K.score+2) :
    B.residual.ncard=2*matchingEdges (G.induce B.residual)+B.actualRoots.ncard+K.score+2+K.rootDefect K.T := by
  have old := B.old_roots_inside
  have eq : B.oldRoots∪B.residual=K.support := by
    ext x
    constructor
    · rintro (a|r);exact old a;exact r.1
    · intro h;by_cases a:x∈B.oldRoots;exact Or.inl a;exact Or.inr ⟨h,a⟩
  have dis : Disjoint B.oldRoots B.residual := Set.disjoint_left.mpr (fun _ a r => r.2 a)
  have count := Set.ncard_union_eq dis
  rw [eq] at count
  have ports : B.actualRoots.ncard=B.oldRoots.ncard+K.targetPorts := by
    change (B.oldRoots∪K.exteriorTargetEnds).ncard=_
    rw [Set.ncard_union_eq (K.disjoint_ends.mono_left old),K.exterior_end_count cap M hm attained]
  have inner := (K.exact_support_matching_rank cap M hm attained).2.1
  change 2*matchingEdges (G.induce K.support)+K.score+2+K.rootDefect K.T+K.targetPorts=K.support.ncard at inner
  have piece := (B.exact_region_matching_partition cap M hm best attained).1
  have rank := K.incident_piece_rank cap M hm attained
  omega
end InnerBarrier

#print axioms defect_add_disjoint
#print axioms defect_mono
#print axioms InnerBarrier.residual_original_defect
#print axioms InnerBarrier.residual_order_identity
end JSP452Audit.StarHost.TenOuterCut
