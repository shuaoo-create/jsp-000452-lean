import OrdinaryRegionContainsClosedUnion
import ProtectedCoreRankAndExposure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem induced_rank_le_of_subset {X : Type*} [Finite X] (G : SimpleGraph X) {U V : Set X}
    (sub : U⊆V) : matchingEdges (G.induce U)≤matchingEdges (G.induce V) := by
  let e : G.induce U ↪g G.induce V := {
    toFun := fun x => ⟨x.val,sub x.property⟩
    inj' := fun _ _ eq => Subtype.ext (congrArg (fun z:↥V => z.val) eq)
    map_rel_iff' := Iff.rfl }
  exact rank_mono_embedding e

theorem closed_union_matching_split {X : Type*} [Finite X] (G : SimpleGraph X) (U : Set X)
    (closed : ∀v∈U,∀w,G.Adj v w → w∈U) :
    matchingEdges G=matchingEdges (G.induce U)+matchingEdges (G.induce Uᶜ) := by
  have split := rank_split_regions G Set.univ U Uᶜ (Set.union_compl_self _) disjoint_compl_right
    (fun v hv w hw edge => hw (closed v hv w edge))
  rwa [rank_eq_of_graph_iso (induceUnivIso G)] at split

theorem strict_closed_union_lengths (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (U : Set F.X) (closed : ∀v∈U,∀w,F.G.Adj v w → w∈U)
    (full : ∀v∈U,Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1) :
    let P := matchingEdges (F.G.induce U)
    P+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges (F.G.induce Uᶜ) := by
  intro P
  obtain ⟨K,sub⟩ := ordinary_region_covers_closed_full_set F.G _ U closed full
  obtain ⟨len,ext⟩ := (strict_only_double_escape F paid).2.2 K
  have inside := induced_rank_le_of_subset F.G sub
  rw [ordinary_region_internal_root_rank F.G _ K] at inside
  have out : K.rest⊆Uᶜ := by
    intro v hv hu
    rcases sub hu with hc|hr
    · exact hv (Or.inr hc)
    · exact hv (Or.inl hr)
  exact ⟨by change P≤_ at inside;clear * - len inside;omega,ext.trans (induced_rank_le_of_subset F.G out)⟩

#print axioms induced_rank_le_of_subset
#print axioms closed_union_matching_split
#print axioms strict_closed_union_lengths
end JSP452Audit.StarHost
