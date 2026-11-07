import RankedComponentExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def CompleteExteriorData {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ) : Prop :=
  let H := G.induce K.core
  let B := G.induce K.rest
  let μ := matchingEdges H
  let W := componentBudget H n
  let a := K.roots.ncard
  1≤W.loss ∧ W.loss≤μ ∧
    ForcingRow B W.len t (padDemand (W.entries n)) (padDemand m) (r+a) ∧
    rowCount W.len t (r+a)=matchingEdges B+d+(μ-W.loss) ∧ rowCount W.len t (r+a)<N ∧
    r+a+d+(μ-W.loss)+1≤min W.len t ∧ max W.len t≤matchingEdges B ∧
    rowEnergy (W.entries n) m (r+a)≤B.edgeSet.ncard

theorem strict_both_complete_exteriors (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    (μ<F.s → CompleteExteriorData F.G K F.n F.m F.r F.rank d) ∧
    (μ<F.t → CompleteExteriorData F.G K F.m F.n F.r F.rank d) := by
  intro μ d
  have D := strict_source_degree_at_least_four F paid
  obtain ⟨big,cheap,_,_⟩ := strict_source_paid_erased_core_successors F paid K
  change diagonal F.n F.m (F.r+2)-1≤2*μ at cheap
  have pos : 0<μ := by omega
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have dh : 2≤d := (minimal_strict_source_deficit F paid).2.2
  have bal : matchingEdges F.G+d=F.rank := by have := (minimal_rank_exact_source F paid).2.2.1;dsimp [d];omega
  constructor
  · intro esc
    exact strict_complete_component_exterior F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K F.row paid
      (nc _) big pos esc d (by omega) bal
  · intro esc
    have same : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have out := strict_complete_component_exterior F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K
      (swap_positive_forcing_row F.G _ _ F.row) (by rw [same];exact paid) (mc _) big pos esc d (by omega) (bal.trans same.symm)
    rw [same] at out
    exact out

private theorem complete_exterior_cover {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ)
    (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (esc : matchingEdges (G.induce K.core)<s) (data : CompleteExteriorData G K n m r N d)
    (C : Set X) (cover : G.IsVertexCover C) :
    matchingEdges (G.induce K.rest)+d+(matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)
      ≤(K.rest∩C).ncard := by
  let W := componentBudget (G.induce K.core) n
  obtain ⟨_,hi,real,rank,_,_⟩ := data
  change W.loss≤matchingEdges (G.induce K.core) at hi
  obtain ⟨sub,count⟩ := cover_induced_ncard G K.rest C cover
  rw [←count,←rank]
  exact forcing_row_cover_length (by dsimp [RemovalBudget.len];omega) ht _ m
    (W.entries_antitone n hn) hm (W.entries_positive n pn) pm _ real _ sub

/-- The extra exterior rank is retained by every cover of the original
graph. It therefore pays that many further genuinely mixed columns. -/
theorem strict_complete_mixed_surplus (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := F.G.induce K.core
    let μ := matchingEdges H
    (μ<F.s → minimumExposure F.G D+(μ-(componentBudget H F.n).loss)<(mixedOffsets F.n F.m F.r).card) ∧
    (μ<F.t → minimumExposure F.G D+(μ-(componentBudget H F.m).loss)<(mixedOffsets F.n F.m F.r).card) := by
  intro D H μ
  let a := K.roots.ncard
  let k := matchingEdges (F.G.induce K.rest)
  let d := F.rank-matchingEdges F.G
  obtain ⟨_,_,small,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=a+μ+k at rank
  have orig : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have large : 4≤D := strict_source_degree_at_least_four F paid
  have live := F.live
  have legal : F.r+F.rank≤F.s+F.t-1 := by dsimp [StrictFamily.rank,rowCount] at *;omega
  obtain ⟨ac,ab,cb,_⟩ := region_partition F.G K.barrier K.pieces
  have use (δ:ℕ) (ext : ∀C,F.G.IsVertexCover C → k+d+δ≤(K.rest∩C).ncard) :
      minimumExposure F.G D+δ<(mixedOffsets F.n F.m F.r).card := by
    have all (C:Set F.X) (cover:F.G.IsVertexCover C) : F.rank+(minimumExposure F.G D+δ)≤C.ncard := by
      have core := core_cover_and_roots F.G K (by change 0<D;omega) cap C cover
      change μ+a+minimumExposure F.G D≤(K.core∩C).ncard+(K.roots∩C).ncard at core
      have outside := ext C cover
      have ac' := ac.mono (Set.inter_subset_left (t:=C)) (Set.inter_subset_left (t:=C))
      have ab' := ab.mono (Set.inter_subset_left (t:=C)) (Set.inter_subset_left (t:=C))
      have cb' := cb.mono (Set.inter_subset_left (t:=C)) (Set.inter_subset_left (t:=C))
      have size := Set.ncard_le_ncard (show (K.roots∩C)∪(K.core∩C)∪(K.rest∩C)⊆C from
        Set.union_subset (Set.union_subset Set.inter_subset_right Set.inter_subset_right) Set.inter_subset_right)
      rw [Set.ncard_union_eq (Disjoint.union_left ab' cb'),Set.ncard_union_eq ac'] at size
      change (K.roots∩C).ncard+(K.core∩C).ncard+(K.rest∩C).ncard≤C.ncard at size;omega
    have price := cover_deletion_row_sum F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.rank
      (minimumExposure F.G D+δ) legal F.row all
    have area := energy_le_deletion_and_mixed F.n F.m F.r
    change rowEnergy F.n F.m F.r≤(∑z∈Finset.range F.rank,deletionColumn F.n F.m (F.r+z))+(mixedOffsets F.n F.m F.r).card at area
    have bad := F.strict;omega
  obtain ⟨red,blue⟩ := strict_both_complete_exteriors F paid K
  exact ⟨fun esc => use _ (complete_exterior_cover F.G K F.n F.m F.r F.rank d F.ht F.hn F.hm F.pn F.pm esc (red esc)),
    fun esc => use _ (complete_exterior_cover F.G K F.m F.n F.r F.rank d F.hs F.hm F.hn F.pm F.pn esc (blue esc))⟩

#print axioms strict_both_complete_exteriors
#print axioms strict_complete_mixed_surplus
end JSP452Audit.StarHost
