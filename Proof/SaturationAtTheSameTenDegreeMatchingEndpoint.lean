import SeparateActualExteriorPortsInTheTokenAccount
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem matching_endpoint_saturation (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    let R := M.spanningCoe
    let N := G \ R
    let W := exposedFull G M 10
    K.S⊆M.verts ∧ W⊆K.T∪K.core ∧ originalDegreeSum N K.T=9*K.T.ncard+(K.T∩W).ncard ∧
      crossCount R K.S K.supportᶜ=0 ∧ crossCount N K.T K.supportᶜ=0 ∧
      (R.induce K.S).edgeSet.ncard=0 ∧ (N.induce K.T).edgeSet.ncard=0 := by
  intro R N W
  have red := Set.ncard_le_ncard (Set.inter_subset_left (s:=K.S) (t:=M.verts))
  have blue := ten_complement_degree_budget M hm cap K.T
  change originalDegreeSum N K.T≤9*K.T.ncard+(K.T∩W).ncard at blue
  have off : Disjoint K.T K.core := disjoint_compl_right.mono Set.subset_union_right K.core_outside
  have dis : Disjoint (K.T∩W) (K.core∩W) := off.mono Set.inter_subset_left Set.inter_subset_left
  have into : (K.T∩W)∪(K.core∩W)⊆W := Set.union_subset Set.inter_subset_right Set.inter_subset_right
  have bound := Set.ncard_le_ncard into
  rw [Set.ncard_union_eq dis] at bound
  have ledger := K.matching_token_account cap M hm
  change K.pieces.ncard+crossCount G K.T K.S+2*(R.induce K.S).edgeSet.ncard+2*(N.induce K.T).edgeSet.ncard+
    crossCount R K.S K.supportᶜ+crossCount N K.T K.supportᶜ≤(K.S∩M.verts).ncard+originalDegreeSum N K.T+(K.core∩W).ncard at ledger
  have score := K.actual
  rw [uniform_factor_cut_on_original] at score
  change (K.pieces.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-7*(K.T.ncard:ℤ)=(K.score:ℤ) at score
  have imbalance := K.imbalance
  change W.ncard=K.score+2 at attained
  have covered : K.S∩M.verts=K.S := Set.eq_of_subset_of_ncard_le Set.inter_subset_left (by omega)
  have counted : (K.T∩W)∪(K.core∩W)=W := Set.eq_of_subset_of_ncard_le into (by rw [Set.ncard_union_eq dis];omega)
  refine ⟨fun x hx => ((show x∈K.S∩M.verts from covered.symm ▸ hx)).2,?_,by omega,by omega,by omega,by omega,by omega⟩
  rw [←counted]
  exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_left

#print axioms matching_endpoint_saturation
end JSP452Audit.StarHost.TenOuterCut
