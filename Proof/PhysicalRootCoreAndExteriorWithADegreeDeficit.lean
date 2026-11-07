import OriginalVertexSetsInTheSumOfTwoHosts
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

structure TenBlockPartition {X:Type u} [Finite X] (G:SimpleGraph X) where
  roots : Set X
  core : Set X
  rest : Set X
  eta : ℕ
  epsilon : ℕ
  rootsCore : Disjoint roots core
  rootsRest : Disjoint roots rest
  coreRest : Disjoint core rest
  cover : roots∪core∪rest=Set.univ
  apart : ∀x∈core,∀y∈rest,¬G.Adj x y
  rank : matchingEdges G=roots.ncard+matchingEdges (G.induce core)+matchingEdges (G.induce rest)
  order : core.ncard=2*matchingEdges (G.induce core)+roots.ncard+eta
  degrees : originalDegreeSum G core+epsilon=10*core.ncard
  critical : OddCriticalFamily (G.induce core)

namespace TenBlockPartition
theorem from_outer_cut {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G) (B:K.InnerBarrier)
    (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (M:G.Subgraph) (hm:M.IsMatching) (best:M.edgeSet.ncard=matchingEdges G)
    (sat:(exposedFull G M 10).ncard=K.score+2) (one:K.score=1) :
    ∃P:TenBlockPartition G,P.roots=B.actualRoots ∧ P.core=B.residual ∧ P.rest=K.remainder ∧
      P.eta=3+K.rootDefect K.T ∧ P.epsilon≤K.rootDefect K.T ∧ K.rootDefect K.T≤2 := by
  obtain ⟨ac,ar,cr,whole,apart⟩ := B.physical_partition
  have rank := (B.exact_region_matching_partition cap M hm best sat).2.1
  have order := B.residual_order_identity cap M hm best sat
  have defic := B.residual_original_defect cap none
  have lim := degree_sum_le_cap G B.residual 10 (fun x _ => cap x)
  let e := K.rootDefect B.residual
  have fee : originalDegreeSum G B.residual+e=10*B.residual.ncard := by
    change originalDegreeSum G B.residual+(10*B.residual.ncard-originalDegreeSum G B.residual)=_;omega
  have crit := odd_critical_family_of_iso B.residualIso B.critical
  exact ⟨⟨B.actualRoots,B.residual,K.remainder,3+K.rootDefect K.T,e,ac,ar,cr,whole,apart,rank,by omega,fee,crit⟩,
    rfl,rfl,rfl,rfl,defic.1,defic.2⟩

theorem from_nearperfect_regular {X:Type u} [Finite X] (G:SimpleGraph X) (reg:∀x,Nat.card (G.neighborSet x)=10)
    (order:Nat.card X=2*matchingEdges G+1) :
    ∃P:TenBlockPartition G,P.rest=∅ ∧ P.eta=1 ∧ P.epsilon=0 := by
  obtain ⟨S,tight,crit⟩ := exists_critical_barrier G
  have rank := tight_deletes_rank G S S tight Set.Subset.rfl
  have empty : (G.induce (∅:Set X))=⊥ := by ext x;exact x.property.elim
  have cut := Set.ncard_add_ncard_compl S
  refine ⟨⟨S,Sᶜ,∅,1,0,disjoint_compl_right,by simp,by simp,by simp,
    fun _ _ _ mem => mem.elim,?_,by omega,?_,crit⟩,rfl,rfl,rfl⟩
  · rw [empty,matchingEdges_bot,Nat.add_zero];exact rank
  · rw [degree_sum_full G Sᶜ 10 (fun x _ => reg x),Nat.add_zero]

def join {X Y:Type u} [Finite X] [Finite Y] {G:SimpleGraph X} {H:SimpleGraph Y}
    (P:TenBlockPartition G) (Q:TenBlockPartition H) : TenBlockPartition (G⊕g H) where
  roots := sumLabels P.roots Q.roots
  core := sumLabels P.core Q.core
  rest := sumLabels P.rest Q.rest
  eta := P.eta+Q.eta
  epsilon := P.epsilon+Q.epsilon
  rootsCore := Set.disjoint_left.mpr (by rintro (x|y) a b;exact Set.disjoint_left.mp P.rootsCore a b;exact Set.disjoint_left.mp Q.rootsCore a b)
  rootsRest := Set.disjoint_left.mpr (by rintro (x|y) a b;exact Set.disjoint_left.mp P.rootsRest a b;exact Set.disjoint_left.mp Q.rootsRest a b)
  coreRest := Set.disjoint_left.mpr (by rintro (x|y) a b;exact Set.disjoint_left.mp P.coreRest a b;exact Set.disjoint_left.mp Q.coreRest a b)
  cover := by
    apply Set.eq_univ_of_forall
    rintro (x|y)
    · exact (P.cover.symm ▸ (Set.mem_univ x) : x∈P.roots∪P.core∪P.rest)
    · exact (Q.cover.symm ▸ (Set.mem_univ y) : y∈Q.roots∪Q.core∪Q.rest)
  apart := by
    rintro (x|x) cx (y|y) cy e
    · exact P.apart x cx y cy e
    · exact not_adj_sum_inl_inr x y e
    · exact not_adj_sum_inl_inr y x e.symm
    · exact Q.apart x cx y cy e
  rank := by rw [matchingEdges_sumGraph,sum_labels_count,sum_labels_rank,sum_labels_rank,P.rank,Q.rank];omega
  order := by rw [sum_labels_count,sum_labels_count,sum_labels_rank,P.order,Q.order];omega
  degrees := by rw [sum_labels_original_degrees,sum_labels_count];have a := P.degrees;have b := Q.degrees;omega
  critical := odd_critical_family_of_iso (inducedSumLabelsIso G H P.core Q.core) (odd_critical_family_sum _ _ P.critical Q.critical)

end TenBlockPartition
#print axioms TenBlockPartition.from_outer_cut
#print axioms TenBlockPartition.from_nearperfect_regular
#print axioms TenBlockPartition.join
end JSP452Audit.StarHost
